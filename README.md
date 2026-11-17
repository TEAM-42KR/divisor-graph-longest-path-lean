# Rule H+ in the divisor graph

A Lean research supplement for finite path rearrangement and insertion in the divisor graph. Two distinct positive integers are adjacent when one divides the other. A table path begins at 1, ends at 2, has no repeated vertex, and has comparable consecutive vertices. Its range is an integer bound on its vertices.

This library belongs to Sungsoo Na's paper on a lower bound for the longest path in the divisor graph, whose section on formal verification describes it.

This is a proved library with a checked statement overview, rather than a collection of standalone problems. `PublicStatements.lean` presents the nine statements below, with their binder and type texts unchanged, and closes each by the corresponding proved constant in `DivisorGraphRuleH`. The proofs and their dependencies are included in the library. `Challenge.lean` and `Solution.lean` are empty compatibility modules; they do not present nine additional problems.

## Theorems and scope

| Statement | Content |
| --- | --- |
| `R0` | The penultimate vertex of a table path with at least three vertices is even and at least 4. |
| `H1` | A prescribed feasible route permutes all indices, has the requested endpoints, and gives a divisor path through the same vertices. |
| `H2` | When the second vertex is odd, shortening at the first subsequent even vertex preserves the required table-path properties. |
| `H3` | A successful ordered search yields a valid route, distinct optional free links, the required divisibilities, and the stated endpoint restrictions. |
| `H4` | An even second vertex gives feasibility for every distinct pair of indices and existence of a search result for every admissible slot. |
| `H5` | A nonempty ordered pool of valid table paths supplies an offered block for an admissible slot. |
| `H5_directory` | The pool-directory hypotheses imply nonemptiness and existence of an offer throughout the specified range. |
| `C_local` | A successful route gives the framed divisor-chain insertion, distinct scaled cofactors, bounds, and the length/gain identities. |
| `C_offer` | A returned offered block has the corresponding path, search, insertion, bound, and length/gain properties. |

The slot, path-validity, feasibility, positivity, and pool-directory hypotheses are part of the statements, not facts inferred from the data. In particular, this supplement does not prove the pool-directory hypotheses for every stored table, establish a full-table computation, or prove an asymptotic bound for the longest divisor-graph path. The scaled-cofactor statements use the factor `p * N` with the positivity and range hypotheses shown in the Lean types.

## Source map

- `RuleHRelease/Definitions/Core.lean`: graph paths, slots, the ordered rules, offers, directories, and insertion observables.
- `Foundation.lean`, `Arithmetic.lean`, `IndexWords.lean`, and `IndexSpecification.lean` in that directory: list, arithmetic, and index-order lemmas.
- `ForwardRoutes.lean`, `RoutePaths.lean`, `Shortening.lean`, `RouteValidity.lean`, `OrderedSearch.lean`, `CofactorPaths.lean`, `Feasibility.lean`, and `RouteExistence.lean`: the route and search results.
- `Offers.lean`, `Directories.lean`, and `LocalInsertion.lean`: ordered-pool choice, directory consequences, and local insertion.
- `ExecutableSequences.lean`, `ExecutableOffers.lean`, and `ExecutableDirectoryIndices.lean`: executable definitions. `SequenceRefinements.lean` and `OfferRefinements.lean` contain all 68 equalities and related results connecting them to the mathematical definitions.
- `RuleHRelease/Proofs/OfferSoundness.lean` and `OfferedInsertion.lean`, with the corresponding files in `RuleHRelease/Theorems/`: offered-block soundness and its insertion consequence.
- `PublicStatements.lean`: the nine checked restatements. `ExactStatements.lean` supplies a second typed statement check. `RequiredAxioms.lean` checks all 214 original results; `Audit.lean` and `Check.lean` provide library consistency and axiom checks.
- `Main.lean`: the JSON-lines executable. `data/` and `scripts/compare.py`: finite comparison inputs, retained outputs, and reproduction instructions.

The axiom allowance is exactly `propext`, `Classical.choice`, and `Quot.sound`. No additional axiom or unchecked native proof computation is used. The sample files are not imported by a theorem.

## Build and reproduction

The pin is Lean `v4.33.1` and Mathlib `v4.33.1`, commit `0df444a360eaa60ab8c11dca51a86af692955474`. `lean-toolchain` and `lake-manifest.json` fix the toolchain and dependency revisions. With Lean's toolchain manager installed, run these commands from the repository root:

```sh
lake exe cache get
lake build
lake env lean Check.lean
python3 scripts/compare.py
```

The default build includes every public Lean module, the statement overview, the axiom checks, and the `ruleH` executable. The last command validates the already recorded comparisons without running the search again. It uses Python's standard library only. To reproduce one small search with a non-empty pool that already has a retained observation (range 6), use the compiled Lean executable:

```sh
python3 scripts/compare.py --replay 1024
```

That command reconstructs the ordered pool from the included paths and sends one JSON request to `.lake/build/bin/ruleH`. The helper compares every retained result field for this small non-empty-pool search, including the four signed projected values. The script does not implement the mathematical search in Python. See the data section below for field meanings and the input format. Replaying larger inputs can take substantial time.

## Finite comparison and its limit

**1,442 of 1,644 selected shape-range pairs were compared: 0 mismatches; 202 were not completed.** All 1,439 selected pairs with range below 10,000 were compared, and 3 of the 205 selected pairs with range 10,000 were compared. The 202 keys whose comparisons were not completed all have range 10,000 and are listed explicitly in `data/comparison.json`, under `not_completed`, by sample identifier and `(size, d, type, index, s)`.

The executable definitions are a literal direct transcription and are too slow at the full range. The first remaining large input was observed running natively for more than 3,606 seconds without returning. This is not a claim that each of the 202 inputs whose comparisons were not completed was individually run until a timeout. An input whose comparison was not completed is not an agreement. These retained comparisons are not a full-table check, and no theorem depends on the sample or its data.

## Finite divisor-graph comparison

The scale is T = 10000 and the fixed selection seed is 20261116. There are 1644 selected shape-range pairs, 1442 retained observations, and 202 pairs not completed. Among the 205 selected pairs at s = 10000, only 3 have observations. All 1439 selected pairs with s < 10000 have observations. All 1442 observed four-field projections agree with their selected expected values. The 202 missing results are not agreements and were not each individually observed to time out. The data are regression evidence, not premises of a Lean theorem or a full-table verification.

### Selected pairs and comparisons not completed

`data/comparison.json` records `selection`, `query_order`, `observed_order`, and `not_completed`. Each selected record has a sample `id`, an original zero-based `row_index`, a row `(size, d, type, index, beta, betaPrime, lmin)`, a four-part shape `key`, a range `s`, a zero-based ordered `pool`, and four `expected` integer fields. `labels` names the selection strata. The semantic row identity is `(d, type, index)`; the pair key is `(size, d, type, index, s)`. Each of the 202 entries in `not_completed` gives the exact sample identifier and pair key of an input whose comparison was not completed.

A type-1 slot has `a = beta / 2 = d`; the other types have `a = beta`. In all types, `aPrime = betaPrime` and `size = max(beta, betaPrime)`. `in_search_range` means `max(size, 6) <= s <= T`. The retained auxiliary shape parameter is `lmin`.

### Observations and fields

`data/observations.jsonl.gz` decompresses to 1442 JSON lines in the retained observation order. Each has `id`, the shape `key`, `s`, `row = (d, type, index)`, slot metadata, a success flag `ok`, an optional `projection`, and an optional `trace`.

The four fields, in order, are `LH`, `NLH`, `VAR`, `GAM`. They are the number of inner-path vertices, the number of added free links, the shortening indicator (0 or 1), and the gain. For a returned block, `GAM = LH + NLH - 1`. The signed code is `(-2, 0, 0, -2)` when the range is smaller than the slot size and `(-1, 0, 0, -1)` when there is no offer. A nonnull trace records the chosen `inner` path, its zero-based `poolIndex`, the `shortened` flag, and a route with index positions `u`, `w` and optional free vertices `x`, `y`.

### Ordered divisor-graph paths

`data/path_data.npz` contains `vertices` (little-endian unsigned 16-bit integers) and `offsets` (little-endian unsigned 64-bit integers). Path j is `vertices[offsets[j]:offsets[j+1]]`. There are 11181 distinct paths containing 8984731 stored vertices. A divisor-graph edge joins distinct positive integers when one divides the other.

`data/catalog.json.gz` lists the ordered path occurrences and the selected pools. An entry contains `occurrence`, `kind`, `kind_code` (master 0, chain 1), grid point `g`, chain parameter `q` (0 for a master), length `len`, and `path_id`. There are 12190 occurrences and 1265 pools. For the pool at range s, take the entries with `g <= s`, preserving their listed order and all duplicate occurrences. Replace each `path_id` by its stored path. Pool records give `pool`, `s`, `paths`, and `terms_including_duplicate_occurrences`.

The listed occurrence order is decreasing length, master before chain, decreasing g, then decreasing q. Duplicate occurrences remain distinct. Each entry's `occurrence` is its zero-based position, and `path_id` selects one stored path. The catalog supplies the paths and pool memberships in this order.

Only the selected expected cells, retained observations, and ordered divisor-graph path inputs are included.

### Reproduction

Use the build and reproduction commands above from the repository root. The data-validation command checks the retained comparisons without recomputing the search. The single-input command reconstructs the selected ordered pool and calls the compiled executable once.

The executable accepts one JSON object per line with `shape` (`d`, `type`, `index`), signed range `s`, and `pool` (an ordered list of integer paths). A request may instead specify `slot`: type 1 uses `type` and `d`; type 2 also uses `qPrev` and `q`; type 3 also uses `index`. The replay helper uses `shape`. A successful response contains `ok`, `shape`, `key`, `s`, `slot`, `table_code`, `projection`, `observation`, `trace`, `firstA`, `firstB`, and `beforeBLength`. The four-element `projection` uses the field order above; a null projection is decoded with the signed absent-block codes. In `observation`, the inner length is named `L`. The sample identifier and row list belong to the retained comparison records, not the executable response. The helper checks the returned shape, key, range, slot metadata, all four projected values, and every retained trace field. The printed small non-empty-pool example compares every retained field. The full-range search is slow; a missing result is not silently filled in.

## License and acknowledgement

MIT License; see `LICENSE`. Lean, Mathlib, and their dependencies retain their respective licenses.

Assisted by AI.
