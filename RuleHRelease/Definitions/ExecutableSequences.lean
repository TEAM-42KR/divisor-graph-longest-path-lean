import Mathlib
import RuleHRelease.Definitions.Foundation
set_option autoImplicit false

namespace DivisorGraphRuleH.Exec

def _root_.DivisorGraphRuleH.Exec.lastIndex (J : List ℕ) : ℕ := J.length - 1

def _root_.DivisorGraphRuleH.Exec.term (J : List ℕ) (i : ℕ) : ℕ := J.getD i 0

def e (J : List ℕ) (k : ℕ) : Prop := term J k % 2 = 0

instance eDecidable (J : List ℕ) (k : ℕ) : Decidable (e J k) :=
  inferInstanceAs (Decidable (term J k % 2 = 0))

def parity (J : List ℕ) (k : ℕ) : Bool := decide (e J k)

def _root_.DivisorGraphRuleH.Exec.up (lo hi : ℕ) : List ℕ := List.range' lo (hi + 1 - lo)

def _root_.DivisorGraphRuleH.Exec.down (hi lo : ℕ) : List ℕ := (up lo hi).reverse

def _root_.DivisorGraphRuleH.Exec.freeMultiples (J : List ℕ) (s : ℤ) (m : ℕ) : List ℕ :=
  (up m s.toNat).filter (fun c => decide (m ∣ c ∧ (c : ℤ) ≤ s ∧ c ∉ J))

def _root_.DivisorGraphRuleH.Exec.interiorIndices (J : List ℕ) (m : ℕ) : List ℕ :=
  (List.range J.length).filter
    (fun i => decide (1 ≤ i ∧ i < lastIndex J ∧ m ∣ term J i))

def _root_.DivisorGraphRuleH.Exec.forwardH (J : List ℕ) (u w : ℕ) : Option (List ℕ) :=
  let n := lastIndex J
  if ¬ (u < w ∧ w < J.length) then none
  else if u = 0 then
    if w = n then some (up 0 n)
    else if w = 1 then some ([0] ++ down n 1)
    else if e J (w - 1) then some (up 0 (w - 1) ++ down n w)
    else if e J 1 then some ([0] ++ down (w - 1) 1 ++ down n w)
    else none
  else if w = n then some (down u 1 ++ [0] ++ up (u + 1) n)
  else if w = u + 1 then some (down u 1 ++ [0] ++ down n w)
  else if u = 1 then some (up 1 (w - 1) ++ [0] ++ down n w)
  else if e J (w - 1) then
    some (down u 1 ++ [0] ++ up (u + 1) (w - 1) ++ down n w)
  else if e J (u + 1) then
    some (down u 1 ++ [0] ++ down (w - 1) (u + 1) ++ down n w)
  else if e J (u - 1) then
    some (up u (w - 1) ++ [0] ++ up 1 (u - 1) ++ down n w)
  else if e J 1 then
    some (up u (w - 1) ++ [0] ++ down (u - 1) 1 ++ down n w)
  else none

def _root_.DivisorGraphRuleH.Exec.H (J : List ℕ) (u w : ℕ) : Option (List ℕ) :=
  if u < w then forwardH J u w
  else if w < u then (forwardH J w u).map List.reverse
  else none

def _root_.DivisorGraphRuleH.Exec.Feasible (J : List ℕ) (u w : ℕ) : Prop := (H J u w).isSome = true

instance feasibleDecidable (J : List ℕ) (u w : ℕ) : Decidable (Feasible J u w) :=
  inferInstanceAs (Decidable ((H J u w).isSome = true))

def feasible (J : List ℕ) (u w : ℕ) : Bool := (H J u w).isSome

def _root_.DivisorGraphRuleH.Exec.routeIndices (J : List ℕ) (u w : ℕ) : List ℕ := (H J u w).getD []

def _root_.DivisorGraphRuleH.Exec.routeOrder (J : List ℕ) (u w : ℕ) : List ℕ :=
  (routeIndices J u w).map (term J)

def _root_.DivisorGraphRuleH.Exec.A1 (J : List ℕ) (s : ℤ) (slot : Slot) : Option EndpointOption :=
  let xs := freeMultiples J s (Nat.lcm 2 slot.a)
  if xs = [] then none else some ⟨lastIndex J, some xs⟩

def _root_.DivisorGraphRuleH.Exec.A2 (J : List ℕ) (_s : ℤ) (slot : Slot) : Option EndpointOption :=
  if slot.a ∣ 2 then some ⟨lastIndex J, none⟩ else none

def _root_.DivisorGraphRuleH.Exec.A3 (J : List ℕ) (s : ℤ) (slot : Slot) : Option EndpointOption :=
  if slot.a = 1 then some ⟨0, none⟩
  else if 2 ≤ slot.a then
    let xs := freeMultiples J s slot.a
    if xs = [] then none else some ⟨0, some xs⟩
  else none

def _root_.DivisorGraphRuleH.Exec.B1 (J : List ℕ) (s : ℤ) (slot : Slot) : Option EndpointOption :=
  let ys := freeMultiples J s slot.a'
  if ys = [] then none else some ⟨0, some ys⟩

def _root_.DivisorGraphRuleH.Exec.B2 (J : List ℕ) (s : ℤ) (slot : Slot) : Option EndpointOption :=
  let ys := freeMultiples J s (Nat.lcm 2 slot.a')
  if ys = [] then none else some ⟨lastIndex J, some ys⟩

def _root_.DivisorGraphRuleH.Exec.B3 (J : List ℕ) (_s : ℤ) (slot : Slot) : Option EndpointOption :=
  if slot.a' ∣ 2 then some ⟨lastIndex J, none⟩ else none

def _root_.DivisorGraphRuleH.Exec.startOptions (J : List ℕ) (s : ℤ) (slot : Slot) : List EndpointOption :=
  [A1 J s slot, A2 J s slot, A3 J s slot].filterMap id

def _root_.DivisorGraphRuleH.Exec.endOptions (J : List ℕ) (s : ℤ) (slot : Slot) : List EndpointOption :=
  [B1 J s slot, B2 J s slot, B3 J s slot].filterMap id

def _root_.DivisorGraphRuleH.Exec.R1 (J : List ℕ) (s : ℤ) (slot : Slot) : List Route :=
  (startOptions J s slot).flatMap fun A =>
    (endOptions J s slot).flatMap fun B =>
      if A.index = B.index then [] else
      match A.links, B.links with
      | some xs, some ys =>
        (xs.head?.bind fun x =>
          (ys.find? (fun y => decide (y ≠ x))).map fun y =>
            (⟨some x, A.index, B.index, some y⟩ : Route)).toList
      | _, _ => []

def _root_.DivisorGraphRuleH.Exec.R2 (J : List ℕ) (s : ℤ) (slot : Slot) : List Route :=
  (startOptions J s slot).flatMap fun A =>
    (endOptions J s slot).flatMap fun B =>
      if A.index = B.index then [] else
      match A.links, B.links with
      | some xs, none =>
        (xs.head?.map fun x => (⟨some x, A.index, B.index, none⟩ : Route)).toList
      | none, some ys =>
        (ys.head?.map fun y => (⟨none, A.index, B.index, some y⟩ : Route)).toList
      | _, _ => []

def _root_.DivisorGraphRuleH.Exec.R3 (J : List ℕ) (s : ℤ) (slot : Slot) : List Route :=
  (startOptions J s slot).flatMap fun A =>
    match A.links with
    | none => []
    | some xs => (interiorIndices J slot.a').flatMap fun w =>
      if Feasible J A.index w then
        (xs.head?.map fun x => (⟨some x, A.index, w, none⟩ : Route)).toList
      else []

def _root_.DivisorGraphRuleH.Exec.R4 (J : List ℕ) (s : ℤ) (slot : Slot) : List Route :=
  (interiorIndices J slot.a).flatMap fun u =>
    (endOptions J s slot).flatMap fun B =>
      match B.links with
      | none => []
      | some ys =>
        if Feasible J u B.index then
          (ys.head?.map fun y => (⟨none, u, B.index, some y⟩ : Route)).toList
        else []

def _root_.DivisorGraphRuleH.Exec.noLinkStarts (J : List ℕ) (s : ℤ) (slot : Slot) : List ℕ :=
  (startOptions J s slot).filterMap
    (fun A => if A.links.isNone then some A.index else none) ++
      interiorIndices J slot.a

def _root_.DivisorGraphRuleH.Exec.noLinkEnds (J : List ℕ) (s : ℤ) (slot : Slot) : List ℕ :=
  (endOptions J s slot).filterMap
    (fun B => if B.links.isNone then some B.index else none) ++
      interiorIndices J slot.a'

def _root_.DivisorGraphRuleH.Exec.R5 (J : List ℕ) (s : ℤ) (slot : Slot) : List Route :=
  (noLinkStarts J s slot).flatMap fun u =>
    (noLinkEnds J s slot).flatMap fun w =>
      if u ≠ w ∧ Feasible J u w then [⟨none, u, w, none⟩] else []

def _root_.DivisorGraphRuleH.Exec.routesOfKind (J : List ℕ) (s : ℤ) (slot : Slot) : RouteKind → List Route
  | .R1 => R1 J s slot
  | .R2 => R2 J s slot
  | .R3 => R3 J s slot
  | .R4 => R4 J s slot
  | .R5 => R5 J s slot

def _root_.DivisorGraphRuleH.Exec.rankedRoutes (J : List ℕ) (s : ℤ) (slot : Slot) : List (RouteKind × Route) :=
  [RouteKind.R1, .R2, .R3, .R4, .R5].flatMap fun kind =>
    (routesOfKind J s slot kind).map fun r => (kind, r)

def _root_.DivisorGraphRuleH.Exec.selectedRoute (J : List ℕ) (s : ℤ) (slot : Slot) : Option Route :=
  (rankedRoutes J s slot).head?.map Prod.snd

def _root_.DivisorGraphRuleH.Exec.cofactors (J : List ℕ) (r : Route) : List ℕ :=
  r.x.toList ++ routeOrder J r.u r.w ++ r.y.toList

def _root_.DivisorGraphRuleH.Exec.linkCount (r : Route) : ℕ := r.x.toList.length + r.y.toList.length

def _root_.DivisorGraphRuleH.Exec.gain (J : List ℕ) (r : Route) : ℕ := J.length - 1 + linkCount r

def _root_.DivisorGraphRuleH.Exec.firstEvenIndex (J : List ℕ) : Option ℕ :=
  (List.range J.length).find? (fun k => decide (e J k))

def _root_.DivisorGraphRuleH.Exec.shortenedPath (J : List ℕ) : Option (List ℕ) :=
  if 2 ≤ lastIndex J ∧ ¬ e J 1 then
    (firstEvenIndex J).map fun k => 1 :: J.drop k
  else none

end DivisorGraphRuleH.Exec
