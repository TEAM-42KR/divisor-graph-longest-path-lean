import Mathlib
set_option autoImplicit false


namespace DivisorGraphRuleH
noncomputable section
attribute [local instance] Classical.propDecidable


def Comparable (a b : ℕ) : Prop := a ∣ b ∨ b ∣ a


def DivisorPath (J : List ℕ) : Prop :=
  (∀ t ∈ J, 0 < t) ∧ J.Nodup ∧ J.IsChain Comparable


def TablePath (J : List ℕ) : Prop :=
  DivisorPath J ∧ J.head? = some 1 ∧ J.getLast? = some 2


def TablePathAt (J : List ℕ) (s : ℤ) : Prop :=
  TablePath J ∧ ∀ t ∈ J, (t : ℤ) ≤ s


def lastIndex (J : List ℕ) : ℕ := J.length - 1


def term (J : List ℕ) (i : ℕ) : ℕ := J.getD i 0


def e (J : List ℕ) (k : ℕ) : Prop := Even (term J k)


def up (lo hi : ℕ) : List ℕ := List.range' lo (hi + 1 - lo)


def down (hi lo : ℕ) : List ℕ := (up lo hi).reverse


def freeMultiples (J : List ℕ) (s : ℤ) (m : ℕ) : List ℕ :=
  (up m s.toNat).filter (fun c => decide (m ∣ c ∧ (c : ℤ) ≤ s ∧ c ∉ J))


def interiorIndices (J : List ℕ) (m : ℕ) : List ℕ :=
  (List.range J.length).filter
    (fun i => decide (1 ≤ i ∧ i < lastIndex J ∧ m ∣ term J i))


def forwardH (J : List ℕ) (u w : ℕ) : Option (List ℕ) :=
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


def H (J : List ℕ) (u w : ℕ) : Option (List ℕ) :=
  if u < w then forwardH J u w
  else if w < u then (forwardH J w u).map List.reverse
  else none


def Feasible (J : List ℕ) (u w : ℕ) : Prop := (H J u w).isSome = true


def routeIndices (J : List ℕ) (u w : ℕ) : List ℕ := (H J u w).getD []


def routeOrder (J : List ℕ) (u w : ℕ) : List ℕ :=
  (routeIndices J u w).map (term J)


def ConsecutiveOddPrimes (qPrev q : ℕ) : Prop :=
  Nat.Prime qPrev ∧ Odd qPrev ∧ Nat.Prime q ∧ Odd q ∧ qPrev < q ∧
    ∀ r, Nat.Prime r → Odd r → qPrev < r → q ≤ r


inductive Slot where
  | type1 (d : ℕ)
  | type2 (qPrev q d : ℕ)
  | type3 (i d : ℕ)
  deriving DecidableEq


def Slot.Valid : Slot → Prop
  | .type1 d => Odd d
  | .type2 qPrev q d => Odd d ∧ ConsecutiveOddPrimes qPrev q
  | .type3 i d => Odd d ∧ 2 ≤ i


def Slot.a : Slot → ℕ
  | .type1 d => d
  | .type2 qPrev _ d => 2 * qPrev * d
  | .type3 i d => 2 ^ i * d


def Slot.a' : Slot → ℕ
  | .type1 d => 3 * d
  | .type2 _ q d => q * d
  | .type3 i d => 2 ^ (i - 1) * d


def Slot.beta : Slot → ℕ
  | .type1 d => 2 * d
  | .type2 qPrev _ d => 2 * qPrev * d
  | .type3 i d => 2 ^ i * d


def Slot.size : Slot → ℕ
  | .type1 d => 3 * d
  | .type2 qPrev _ d => 2 * qPrev * d
  | .type3 i d => 2 ^ i * d


inductive SlotKind where
  | type1 | type2 | type3
  deriving DecidableEq


structure Shape where
  kind : SlotKind
  index : ℕ
  d : ℕ
  deriving DecidableEq


def oddPrime (i : ℕ) : ℕ := Nat.nth Nat.Prime i


def Shape.Valid (sh : Shape) : Prop :=
  Odd sh.d ∧ match sh.kind with
    | .type1 => sh.index = 0
    | .type2 => 2 ≤ sh.index ∧ (sh.d = 1 ∨ oddPrime sh.index ≤ sh.d.minFac)
    | .type3 => 2 ≤ sh.index


def Shape.toSlot (sh : Shape) : Slot :=
  match sh.kind with
  | .type1 => .type1 sh.d
  | .type2 => .type2 (oddPrime (sh.index - 1)) (oddPrime sh.index) sh.d
  | .type3 => .type3 sh.index sh.d


def ShapeAtScale (T : ℕ) (sh : Shape) : Prop :=
  sh.Valid ∧ sh.toSlot.size ≤ T


def SlotKind.code : SlotKind → ℕ
  | .type1 => 1
  | .type2 => 2
  | .type3 => 3


def Shape.key (sh : Shape) : ℕ × ℕ × ℕ × ℕ :=
  (sh.toSlot.size, sh.d, sh.kind.code, sh.index)


structure EndpointOption where
  index : ℕ
  links : Option (List ℕ)
  deriving DecidableEq


def A1 (J : List ℕ) (s : ℤ) (slot : Slot) : Option EndpointOption :=
  let xs := freeMultiples J s (Nat.lcm 2 slot.a)
  if xs = [] then none else some ⟨lastIndex J, some xs⟩


def A2 (J : List ℕ) (_s : ℤ) (slot : Slot) : Option EndpointOption :=
  if slot.a ∣ 2 then some ⟨lastIndex J, none⟩ else none


def A3 (J : List ℕ) (s : ℤ) (slot : Slot) : Option EndpointOption :=
  if slot.a = 1 then some ⟨0, none⟩
  else if 2 ≤ slot.a then
    let xs := freeMultiples J s slot.a
    if xs = [] then none else some ⟨0, some xs⟩
  else none


def B1 (J : List ℕ) (s : ℤ) (slot : Slot) : Option EndpointOption :=
  let ys := freeMultiples J s slot.a'
  if ys = [] then none else some ⟨0, some ys⟩


def B2 (J : List ℕ) (s : ℤ) (slot : Slot) : Option EndpointOption :=
  let ys := freeMultiples J s (Nat.lcm 2 slot.a')
  if ys = [] then none else some ⟨lastIndex J, some ys⟩


def B3 (J : List ℕ) (_s : ℤ) (slot : Slot) : Option EndpointOption :=
  if slot.a' ∣ 2 then some ⟨lastIndex J, none⟩ else none


def startOptions (J : List ℕ) (s : ℤ) (slot : Slot) : List EndpointOption :=
  [A1 J s slot, A2 J s slot, A3 J s slot].filterMap id


def endOptions (J : List ℕ) (s : ℤ) (slot : Slot) : List EndpointOption :=
  [B1 J s slot, B2 J s slot, B3 J s slot].filterMap id


structure Route where
  x : Option ℕ
  u : ℕ
  w : ℕ
  y : Option ℕ
  deriving DecidableEq


def IsRoute (J : List ℕ) (r : Route) : Prop :=
  r.u < J.length ∧ r.w < J.length ∧ r.u ≠ r.w ∧ Feasible J r.u r.w


def R1 (J : List ℕ) (s : ℤ) (slot : Slot) : List Route :=
  (startOptions J s slot).flatMap fun A =>
    (endOptions J s slot).flatMap fun B =>
      if A.index = B.index then [] else
      match A.links, B.links with
      | some xs, some ys =>
        (xs.head?.bind fun x =>
          (ys.find? (fun y => decide (y ≠ x))).map fun y =>
            (⟨some x, A.index, B.index, some y⟩ : Route)).toList
      | _, _ => []


def R2 (J : List ℕ) (s : ℤ) (slot : Slot) : List Route :=
  (startOptions J s slot).flatMap fun A =>
    (endOptions J s slot).flatMap fun B =>
      if A.index = B.index then [] else
      match A.links, B.links with
      | some xs, none =>
        (xs.head?.map fun x => (⟨some x, A.index, B.index, none⟩ : Route)).toList
      | none, some ys =>
        (ys.head?.map fun y => (⟨none, A.index, B.index, some y⟩ : Route)).toList
      | _, _ => []


def R3 (J : List ℕ) (s : ℤ) (slot : Slot) : List Route :=
  (startOptions J s slot).flatMap fun A =>
    match A.links with
    | none => []
    | some xs => (interiorIndices J slot.a').flatMap fun w =>
      if Feasible J A.index w then
        (xs.head?.map fun x => (⟨some x, A.index, w, none⟩ : Route)).toList
      else []


def R4 (J : List ℕ) (s : ℤ) (slot : Slot) : List Route :=
  (interiorIndices J slot.a).flatMap fun u =>
    (endOptions J s slot).flatMap fun B =>
      match B.links with
      | none => []
      | some ys =>
        if Feasible J u B.index then
          (ys.head?.map fun y => (⟨none, u, B.index, some y⟩ : Route)).toList
        else []


def noLinkStarts (J : List ℕ) (s : ℤ) (slot : Slot) : List ℕ :=
  (startOptions J s slot).filterMap
    (fun A => if A.links.isNone then some A.index else none) ++
      interiorIndices J slot.a


def noLinkEnds (J : List ℕ) (s : ℤ) (slot : Slot) : List ℕ :=
  (endOptions J s slot).filterMap
    (fun B => if B.links.isNone then some B.index else none) ++
      interiorIndices J slot.a'


def R5 (J : List ℕ) (s : ℤ) (slot : Slot) : List Route :=
  (noLinkStarts J s slot).flatMap fun u =>
    (noLinkEnds J s slot).flatMap fun w =>
      if u ≠ w ∧ Feasible J u w then [⟨none, u, w, none⟩] else []


inductive RouteKind where
  | R1 | R2 | R3 | R4 | R5
  deriving DecidableEq


def routesOfKind (J : List ℕ) (s : ℤ) (slot : Slot) : RouteKind → List Route
  | .R1 => R1 J s slot
  | .R2 => R2 J s slot
  | .R3 => R3 J s slot
  | .R4 => R4 J s slot
  | .R5 => R5 J s slot


def rankedRoutes (J : List ℕ) (s : ℤ) (slot : Slot) : List (RouteKind × Route) :=
  [RouteKind.R1, .R2, .R3, .R4, .R5].flatMap fun kind =>
    (routesOfKind J s slot kind).map fun r => (kind, r)


def selectedRoute (J : List ℕ) (s : ℤ) (slot : Slot) : Option Route :=
  (rankedRoutes J s slot).head?.map Prod.snd


def SearchReturns (J : List ℕ) (s : ℤ) (slot : Slot) (r : Route) : Prop :=
  selectedRoute J s slot = some r


def cofactors (J : List ℕ) (r : Route) : List ℕ :=
  r.x.toList ++ routeOrder J r.u r.w ++ r.y.toList


def linkCount (r : Route) : ℕ := r.x.toList.length + r.y.toList.length


def gain (J : List ℕ) (r : Route) : ℕ := J.length - 1 + linkCount r


def firstEvenIndex (J : List ℕ) : Option ℕ :=
  (List.range J.length).find? (fun k => decide (e J k))


def FirstEven (J : List ℕ) (k : ℕ) : Prop :=
  k < J.length ∧ e J k ∧ ∀ i, i < k → ¬ e J i


def shortenedPath (J : List ℕ) : Option (List ℕ) :=
  if 2 ≤ lastIndex J ∧ ¬ e J 1 then
    (firstEvenIndex J).map fun k => 1 :: J.drop k
  else none


structure TableBlock where
  inner : List ℕ
  route : Route
  deriving DecidableEq


def directBlock (J : List ℕ) (s : ℤ) (slot : Slot) : Option TableBlock :=
  (selectedRoute J s slot).map fun r => ⟨J, r⟩


def shortBlock (I : List ℕ) (s : ℤ) (slot : Slot) : Option TableBlock :=
  (shortenedPath I).bind fun J => directBlock J s slot


def firstB (pool : List (List ℕ)) (s : ℤ) (slot : Slot) : Option TableBlock :=
  pool.findSome? (fun J => directBlock J s slot)


def beforeB (pool : List (List ℕ)) (s : ℤ) (slot : Slot) : List (List ℕ) :=
  pool.takeWhile (fun J => (selectedRoute J s slot).isNone)


def firstA (pool : List (List ℕ)) (s : ℤ) (slot : Slot) : Option TableBlock :=
  (beforeB pool s slot).findSome? (fun I => shortBlock I s slot)


def offer (pool : List (List ℕ)) (s : ℤ) (slot : Slot) : Option TableBlock :=
  match firstA pool s slot, firstB pool s slot with
  | none, none => none
  | some A, none => some A
  | none, some B => some B
  | some A, some B =>
    if gain B.inner B.route ≤ gain A.inner A.route then some A else some B


inductive PoolOrigin where
  | master
  | chain (q : ℕ)
  deriving DecidableEq


structure PoolEntry where
  origin : PoolOrigin
  grid : ℕ
  path : List ℕ
  isReference : Bool
  deriving DecidableEq


def PoolEntry.eligible (E : PoolEntry) : Prop :=
  E.origin = .master ∨ E.isReference = false


def PoolEntry.masterRank (E : PoolEntry) : ℕ :=
  match E.origin with | .master => 0 | .chain _ => 1


def PoolEntry.prime (E : PoolEntry) : ℕ :=
  match E.origin with | .master => 0 | .chain q => q


def poolBefore (A B : PoolEntry) : Bool := decide
  (B.path.length < A.path.length ∨
   A.path.length = B.path.length ∧
    (A.masterRank < B.masterRank ∨
     A.masterRank = B.masterRank ∧
      (B.grid < A.grid ∨ A.grid = B.grid ∧ B.prime ≤ A.prime)))


structure PoolDirectory where
  scale : ℕ
  entries : List PoolEntry


def pathPool (D : PoolDirectory) (s : ℤ) : List (List ℕ) :=
  (((D.entries.filter (fun E => decide
    (E.eligible ∧ E.grid ≤ D.scale ∧ (E.grid : ℤ) ≤ s))).mergeSort poolBefore).map
      PoolEntry.path)


def PoolHypotheses (D : PoolDirectory) : Prop :=
  3000 ≤ D.scale ∧
  (∀ E ∈ D.entries, E.eligible → E.grid ≤ D.scale →
    TablePath E.path ∧ ∀ c ∈ E.path, c ≤ E.grid) ∧
  ∃ E ∈ D.entries, E.origin = .master ∧ E.grid ≤ 6


def scaledCofactors (N p : ℕ) (block : TableBlock) : List ℕ :=
  (cofactors block.inner block.route).map (fun c => (p * N) * c)


def framedBlock (slot : Slot) (N p : ℕ) (block : TableBlock) : List ℕ :=
  [slot.a * N] ++ scaledCofactors N p block ++ [slot.a' * N]

end
end DivisorGraphRuleH
