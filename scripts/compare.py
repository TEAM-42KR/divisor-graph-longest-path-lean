#!/usr/bin/env python3
"""Validate retained comparisons, or replay one input with the compiled Lean executable."""
import argparse
import array
import ast
import gzip
import json
from pathlib import Path
import struct
import subprocess
import time
import sys
import zipfile

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / 'data'
FIELDS = ['LH', 'NLH', 'VAR', 'GAM']


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load_comparison():
    document = json.loads((DATA / 'comparison.json').read_text())
    require(document['field_order'] == FIELDS, 'unexpected field order')
    records = document['selection']
    selected = {row['id']: row for row in records}
    require(len(selected) == len(records) == 1644, 'selection size or duplicate identifier')
    return document, selected


def projection(observation):
    """Decode the executable response, including its two absent-block codes."""
    if observation['projection'] is not None:
        result = observation['projection']
        require(len(result) == 4, 'projection must have four fields')
        return result
    code = -2 if observation['s'] < observation['slot']['size'] else -1
    return [code, 0, 0, code]


def check_observation(observation, row, retained=True):
    require(observation['ok'] is True, 'unsuccessful executable response')
    if retained:
        require(observation['id'] == row['id'], 'response identifier mismatch')
        require(observation['row'] == [row['d'], row['type'], row['index']], 'response row mismatch')
    else:
        require(observation['shape'] == {'d': row['d'], 'type': row['type'], 'index': row['index']}, 'response shape mismatch')
    require(observation['s'] == row['s'], 'response range mismatch')
    require(observation['key'] == row['key'], 'response shape-key mismatch')
    size, d, typ, index, beta, beta_prime, _ = row['row']
    require(row['key'] == [size, d, typ, index], 'selected key metadata mismatch')
    expected_slot = {'a': beta // 2 if typ == 1 else beta, 'aPrime': beta_prime, 'beta': beta, 'size': size}
    require(all(observation['slot'][k] == v for k, v in expected_slot.items()), 'response slot metadata mismatch')
    if not retained:
        require(observation['slot']['type'] == typ and observation['slot']['d'] == d, 'response slot identity mismatch')
        if typ == 3:
            require(observation['slot']['index'] == index, 'response slot index mismatch')
        want_code = -2 if observation['s'] < size else -1 if observation['projection'] is None else 0
        require(observation['table_code'] == want_code, 'response table code mismatch')
    return projection(observation) == [row['expected'][field] for field in FIELDS]


def verify(document, selected):
    observed = []
    mismatches = []
    with gzip.open(DATA / 'observations.jsonl.gz', 'rt', encoding='ascii') as stream:
        for line in stream:
            observation = json.loads(line)
            identifier = observation['id']
            require(identifier in selected, 'observation outside selection')
            observed.append(identifier)
            if not check_observation(observation, selected[identifier]):
                mismatches.append(identifier)
    require(len(set(observed)) == len(observed), 'duplicate observation')
    require(observed == document['observed_order'], 'observation order mismatch')
    require(set(document['query_order']) == set(selected), 'query order does not cover selection')
    require(len(document['query_order']) == len(selected), 'duplicate query identifier')
    missing = set(selected) - set(observed)
    not_completed = document['not_completed']
    require({row['id'] for row in not_completed} == missing, 'not_completed key mismatch')
    require(len(not_completed) == len(missing), 'duplicate not_completed identifier')
    for row in not_completed:
        original = selected[row['id']]
        require(row['pair_key'] == original['key'] + [original['s']], 'not_completed pair key mismatch')
    below = {identifier for identifier, row in selected.items() if row['s'] < 10000}
    full = {identifier for identifier, row in selected.items() if row['s'] == 10000}
    require(len(below) == 1439 and below <= set(observed), 'below-full-range coverage mismatch')
    require(len(full) == 205 and len(full & set(observed)) == 3, 'full-range coverage mismatch')
    require(missing <= full and len(missing) == 202, 'not_completed range or count mismatch')
    require(len(observed) == 1442 and not mismatches, 'recorded comparison mismatch')
    require(document['sample_complete'] is False, 'incorrect completeness claim')
    return {'selected': len(selected), 'compared': len(observed), 'mismatches': len(mismatches),
            'not_completed': len(missing), 'below_full_range_compared': len(below),
            'full_range_selected': len(full), 'full_range_compared': len(full & set(observed))}


def npy_array(content, descriptor, typecode):
    require(content[:6] == b'\x93NUMPY', 'invalid NumPy array header')
    version = content[6:8]
    if version == b'\x01\x00':
        length = struct.unpack('<H', content[8:10])[0]
        start = 10
    else:
        require(version in (b'\x02\x00', b'\x03\x00'), 'unsupported NumPy array version')
        length = struct.unpack('<I', content[8:12])[0]
        start = 12
    header = ast.literal_eval(content[start:start + length].decode('ascii'))
    require(header['descr'] == descriptor and not header['fortran_order'], 'unexpected array encoding')
    require(len(header['shape']) == 1, 'expected a one-dimensional array')
    values = array.array(typecode)
    values.frombytes(content[start + length:])
    if sys.byteorder != 'little':
        values.byteswap()
    require(len(values) == header['shape'][0], 'array length mismatch')
    return values


def ordered_pool(row):
    with gzip.open(DATA / 'catalog.json.gz', 'rt', encoding='ascii') as stream:
        catalog = json.load(stream)
    with zipfile.ZipFile(DATA / 'path_data.npz') as archive:
        require(archive.namelist() == ['vertices.npy', 'offsets.npy'], 'unexpected path archive members')
        vertices = npy_array(archive.read('vertices.npy'), '<u2', 'H')
        offsets = npy_array(archive.read('offsets.npy'), '<u8', 'Q')
    require(offsets[0] == 0 and offsets[-1] == len(vertices), 'path offset boundary mismatch')
    metadata = catalog['pools'][row['pool']]
    require(metadata['pool'] == row['pool'] and metadata['s'] == row['s'], 'pool metadata mismatch')
    result = []
    for entry in catalog['entries']:
        if entry['g'] <= row['s']:
            identifier = entry['path_id']
            path = list(vertices[offsets[identifier]:offsets[identifier + 1]])
            require(len(path) == entry['len'], 'stored path length mismatch')
            result.append(path)
    require(len(result) == metadata['paths'], 'pool occurrence count mismatch')
    require(sum(map(len, result)) == metadata['terms_including_duplicate_occurrences'], 'pool term count mismatch')
    return result



def retained_observation(identifier):
    with gzip.open(DATA / 'observations.jsonl.gz', 'rt', encoding='ascii') as stream:
        matches = [json.loads(line) for line in stream if json.loads(line)['id'] == identifier]
    require(len(matches) == 1, 'replay requires exactly one retained observation')
    return matches[0]


def compare_retained(response, retained, row, request):
    require(check_observation(retained, row), 'retained expected fields differ')
    require(check_observation(response, row, retained=False), 'Lean expected fields differ')
    require(set(retained) == {'id', 'key', 'ok', 'projection', 'row', 's', 'slot', 'trace'},
            'unrecognized retained observation fields')
    actual = {name: response[name] for name in ('key', 'ok', 'projection', 's', 'trace')}
    actual.update(id=row['id'], row=[response['shape'][name] for name in ('d', 'type', 'index')],
                  slot={name: response['slot'][name] for name in retained['slot']})
    require(actual == retained, 'Lean response differs from retained observation')
    values = retained['projection']
    expected_observation = None if values is None else dict(zip(('L', 'NLH', 'VAR', 'GAM'), values))
    require(response['observation'] == expected_observation, 'Lean observation fields differ')
    all_response_fields_checked = False
    if not request['pool']:
        # For an empty retained pool every diagnostic is absent; no search is implemented here.
        require(row['type'] == 1, 'empty-pool full-response comparison currently requires type 1')
        expected_slot = dict(retained['slot'], type=row['type'], d=row['d'])
        expected = dict(ok=retained['ok'], key=retained['key'], s=retained['s'],
                        shape=request['shape'], slot=expected_slot,
                        table_code=-2 if row['s'] < expected_slot['size'] else -1,
                        projection=retained['projection'], observation=expected_observation,
                        trace=retained['trace'], firstA=None, firstB=None, beforeBLength=0)
        require(response == expected, 'empty-pool Lean response differs in a result field')
        all_response_fields_checked = True
    return {'all_retained_fields_equal': True, 'retained_fields': sorted(retained),
            'four_fields': FIELDS, 'four_values': projection(response),
            'all_response_fields_checked': all_response_fields_checked,
            'response_fields': sorted(response), 'empty_pool_boundary': not request['pool']}


def replay(identifier, selected, executable, timeout):
    require(identifier in selected, 'identifier is not selected')
    row = selected[identifier]
    retained = retained_observation(identifier)
    request = {'shape': {'d': row['d'], 'type': row['type'], 'index': row['index']},
               's': row['s'], 'pool': ordered_pool(row)}
    require(executable.is_file(), 'Lean executable is absent; run lake build first')
    started = time.monotonic()
    completed = subprocess.run([str(executable)], input=json.dumps(request, separators=(',', ':')) + '\n',
                               text=True, capture_output=True, check=True, timeout=timeout)
    lines = [line for line in completed.stdout.splitlines() if line.strip()]
    require(len(lines) == 1, 'expected one Lean response')
    response = json.loads(lines[0])
    require(response['ok'] is True, 'unsuccessful Lean response')
    require(response['shape'] == request['shape'], 'Lean shape response mismatch')
    require(response['key'] == row['key'] and response['s'] == row['s'], 'Lean response key or range mismatch')
    comparison = compare_retained(response, retained, row, request)
    return {'id': identifier, 'key': row['key'], 's': row['s'], 'projection': projection(response),
            'matches': True, 'request': request, 'response': response,
            'retained_observation': retained, 'retained_comparison': comparison,
            'native_argv': [str(executable)], 'native_exit_code': completed.returncode,
            'native_elapsed_s': time.monotonic() - started, 'native_stderr': completed.stderr}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--replay', type=int, metavar='ID', help='call the real Lean executable for one selected input')
    parser.add_argument('--executable', type=Path, default=ROOT / '.lake/build/bin/ruleH')
    parser.add_argument('--timeout', type=float, default=120, help='seconds allowed for a single Lean request')
    args = parser.parse_args()
    document, selected = load_comparison()
    if args.replay is None:
        result = verify(document, selected)
    else:
        result = replay(args.replay, selected, args.executable.resolve(), args.timeout)
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
