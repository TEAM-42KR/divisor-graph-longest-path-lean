import RuleHRelease.Heads
import Solution
import Lean


open Lean Elab Command

elab "#repo_audit" : command => do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let expected : List Name := []

  let heads : List (Name × Bool) := [(``RuleHRelease.C_offer, false)]
  for (h, allowSorry) in heads do
    let axs := (← liftCoreM <| Lean.collectAxioms h).toList
    logInfo m!"AUDIT axioms {h}: {axs} (sorryAx allowed: {allowSorry})"
    for a in axs do
      unless std.contains a || (allowSorry && a == ``sorryAx) do
        logError m!"AUDIT FAIL {h}: forbidden axiom {a}"
  let mods := env.header.moduleNames
  let direct := env.constants.map₁.fold (init := (#[] : Array Name)) fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some idx =>
      if (mods[idx.toNat]!.getRoot == `RuleHRelease || false) && ci.getUsedConstantsAsSet.contains ``sorryAx then
        acc.push n
      else acc
    | none => acc
  let found := (direct.qsort Name.lt).toList
  let want := (expected.toArray.qsort Name.lt).toList
  logInfo m!"AUDIT placeholders ({found.length}): {found}"
  unless found == want do
    logError m!"AUDIT FAIL placeholder mismatch (direct sorryAx users ≠ open nodes): found {found}, expected {want}"

#repo_audit
