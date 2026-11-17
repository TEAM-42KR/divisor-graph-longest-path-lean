import Mathlib
import RuleHRelease.Definitions.ExecutableDirectoryIndices

set_option autoImplicit false

open Lean

namespace DivisorGraphRuleH.OfferRefinements.Cli
open DivisorGraphRuleH

private def natOptionJson : Option ℕ → Json
  | none => Json.null
  | some n => toJson n

private def slotJson (slot : Slot) : Json :=
  let common := [("a", toJson slot.a), ("aPrime", toJson slot.a'),
    ("beta", toJson slot.beta), ("size", toJson slot.size)]
  Json.mkObj (common ++ match slot with
    | .type1 d => [("type", toJson (1 : ℕ)), ("d", toJson d)]
    | .type2 qPrev q d => [("type", toJson (2 : ℕ)), ("qPrev", toJson qPrev),
        ("q", toJson q), ("d", toJson d)]
    | .type3 i d => [("type", toJson (3 : ℕ)), ("index", toJson i), ("d", toJson d)])

private def shapeJson (sh : Shape) : Json :=
  Json.mkObj [("d", toJson sh.d), ("type", toJson sh.kind.code), ("index", toJson sh.index)]

private def keyJson (sh : Shape) : Json :=
  let k := Exec.shapeKeyFast sh
  toJson [k.1, k.2.1, k.2.2.1, k.2.2.2]

private def routeJson (r : Route) : Json :=
  Json.mkObj [("x", natOptionJson r.x), ("u", toJson r.u),
    ("w", toJson r.w), ("y", natOptionJson r.y)]

private def traceJson : Option Exec.OfferTrace → Json
  | none => Json.null
  | some t => Json.mkObj [("poolIndex", toJson t.poolIndex),
      ("shortened", toJson t.shortened), ("inner", toJson t.block.inner),
      ("route", routeJson t.block.route)]

private def observationJson : Option Exec.OfferTrace → Json
  | none => Json.null
  | some t =>
    let o := Exec.observeTrace t
    Json.mkObj [("L", toJson o.innerLength), ("NLH", toJson o.links),
      ("VAR", toJson (if o.shortened then (1 : ℕ) else 0)), ("GAM", toJson o.gain)]

private def parseShape (j : Json) : Except String Shape := do
  let d ← j.getObjValAs? ℕ "d"
  let typ ← j.getObjValAs? ℕ "type"
  let i ← j.getObjValAs? ℕ "index"
  match Exec.shapeOfRow d typ i with
  | none => throw "shape.type must be 1, 2 or 3"
  | some sh => pure sh

private def parseSlot (j : Json) : Except String Slot := do
  let d ← j.getObjValAs? ℕ "d"
  let typ ← j.getObjValAs? ℕ "type"
  match typ with
  | 1 => pure (.type1 d)
  | 2 => pure (.type2 (← j.getObjValAs? ℕ "qPrev") (← j.getObjValAs? ℕ "q") d)
  | 3 => pure (.type3 (← j.getObjValAs? ℕ "index") d)
  | _ => throw "slot.type must be 1, 2 or 3"

private def inputSlot (j : Json) : Except String (Slot × Option Shape) := do
  match j.getObjVal? "shape" with
  | .ok v =>
    let sh ← parseShape v
    pure (Exec.toSlotFast sh, some sh)
  | .error _ => pure (← parseSlot (← j.getObjVal? "slot"), none)

private def shapeFields (slot : Slot) (sh : Option Shape) : List (String × Json) :=
  [("slot", slotJson slot), ("shape", sh.map shapeJson |>.getD Json.null),
    ("key", sh.map keyJson |>.getD Json.null)]


def handle (j : Json) : Except String Json := do
  let op := (j.getObjValAs? String "op").toOption.getD "offer"
  if op = "boundedPrimes" then
    let bound ← j.getObjValAs? ℕ "bound"
    return Json.mkObj [("ok", toJson true), ("bound", toJson bound),
      ("values", toJson (Exec.primesUpTo bound))]
  if op = "primes" then
    let indices ← j.getObjValAs? (List ℕ) "indices"
    return Json.mkObj [("ok", toJson true), ("indices", toJson indices),
      ("values", toJson (indices.map Exec.oddPrimeFast))]
  let (slot, sh) ← inputSlot j
  if op = "shape" then
    return Json.mkObj ([("ok", toJson true)] ++ shapeFields slot sh)
  if op ≠ "offer" then throw "op must be offer, shape, primes or boundedPrimes"
  let pool ← j.getObjValAs? (List (List ℕ)) "pool"
  let s ← j.getObjValAs? ℤ "s"
  let A := Exec.firstATrace pool s slot
  let B := Exec.firstBTrace pool s slot
  let chosen := Exec.chooseTrace A B
  let code : ℤ := if s < (slot.size : ℤ) then -2 else if chosen.isNone then -1 else 0
  let projection := chosen.map fun t =>
    let o := Exec.observeTrace t
    toJson [o.innerLength, o.links, if o.shortened then (1 : ℕ) else 0, o.gain]
  return Json.mkObj ([("ok", toJson true), ("s", toJson s),
    ("table_code", toJson code), ("observation", observationJson chosen),
    ("projection", projection.getD Json.null), ("trace", traceJson chosen),
    ("firstA", traceJson A), ("firstB", traceJson B),
    ("beforeBLength", toJson (Exec.beforeB pool s slot).length)] ++ shapeFields slot sh)

end DivisorGraphRuleH.OfferRefinements.Cli

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let out ← IO.getStdout
  for line in input.splitOn "\n" do
    if !line.trimAscii.toString.isEmpty then
      let result := Lean.Json.parse line >>= DivisorGraphRuleH.OfferRefinements.Cli.handle
      let response := match result with
        | .ok value => value
        | .error message => Lean.Json.mkObj [("ok", Lean.toJson false), ("error", Lean.toJson message)]
      out.putStrLn response.compress
