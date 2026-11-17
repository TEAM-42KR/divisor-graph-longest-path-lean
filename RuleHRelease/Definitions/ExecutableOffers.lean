import Mathlib
import RuleHRelease.Definitions.SequenceRefinements
set_option autoImplicit false

namespace DivisorGraphRuleH.Exec

def _root_.DivisorGraphRuleH.Exec.directBlock (J : List ℕ) (s : ℤ) (slot : Slot) : Option TableBlock :=
  (selectedRoute J s slot).map fun r => ⟨J, r⟩

def _root_.DivisorGraphRuleH.Exec.shortBlock (I : List ℕ) (s : ℤ) (slot : Slot) : Option TableBlock :=
  (shortenedPath I).bind fun J => directBlock J s slot

def _root_.DivisorGraphRuleH.Exec.firstB (pool : List (List ℕ)) (s : ℤ) (slot : Slot) : Option TableBlock :=
  pool.findSome? (fun J => directBlock J s slot)

def _root_.DivisorGraphRuleH.Exec.beforeB (pool : List (List ℕ)) (s : ℤ) (slot : Slot) : List (List ℕ) :=
  pool.takeWhile (fun J => (selectedRoute J s slot).isNone)

def _root_.DivisorGraphRuleH.Exec.firstA (pool : List (List ℕ)) (s : ℤ) (slot : Slot) : Option TableBlock :=
  (beforeB pool s slot).findSome? (fun I => shortBlock I s slot)

def chooseBlock (A B : Option TableBlock) : Option TableBlock :=
  match A, B with
  | none, none => none
  | some A, none => some A
  | none, some B => some B
  | some A, some B =>
    if gain B.inner B.route ≤ gain A.inner A.route then some A else some B

def offerExec (pool : List (List ℕ)) (s : ℤ) (slot : Slot) : Option TableBlock :=
  chooseBlock (firstA pool s slot) (firstB pool s slot)

structure OfferTrace where
  poolIndex : ℕ
  shortened : Bool
  block : TableBlock
  deriving DecidableEq

def taggedFindSome (f : List ℕ → Option TableBlock) (flag : Bool)
    (offset : ℕ) : List (List ℕ) → Option OfferTrace
  | [] => none
  | J :: rest =>
    match f J with
    | some block => some ⟨offset, flag, block⟩
    | none => taggedFindSome f flag (offset + 1) rest

def firstBTrace (pool : List (List ℕ)) (s : ℤ) (slot : Slot) : Option OfferTrace :=
  taggedFindSome (fun J => directBlock J s slot) false 0 pool

def firstATrace (pool : List (List ℕ)) (s : ℤ) (slot : Slot) : Option OfferTrace :=
  taggedFindSome (fun J => shortBlock J s slot) true 0 (beforeB pool s slot)

def chooseTrace (A B : Option OfferTrace) : Option OfferTrace :=
  match A, B with
  | none, none => none
  | some A, none => some A
  | none, some B => some B
  | some A, some B =>
    if gain B.block.inner B.block.route ≤ gain A.block.inner A.block.route
    then some A else some B

def offerTrace (pool : List (List ℕ)) (s : ℤ) (slot : Slot) : Option OfferTrace :=
  chooseTrace (firstATrace pool s slot) (firstBTrace pool s slot)


def oddPrimeExec : ℕ → ℕ
  | 0 => 2
  | i + 1 => Nat.find (Nat.exists_infinite_primes (oddPrimeExec i + 1))

def toSlotExec (sh : Shape) : Slot :=
  match sh.kind with
  | .type1 => .type1 sh.d
  | .type2 => .type2 (oddPrimeExec (sh.index - 1)) (oddPrimeExec sh.index) sh.d
  | .type3 => .type3 sh.index sh.d

def shapeSizeExec (sh : Shape) : ℕ :=
  match sh.kind with
  | .type1 => 3 * sh.d
  | .type2 => 2 * oddPrimeExec (sh.index - 1) * sh.d
  | .type3 => 2 ^ sh.index * sh.d

def shapeKeyExec (sh : Shape) : ℕ × ℕ × ℕ × ℕ :=
  (shapeSizeExec sh, sh.d, sh.kind.code, sh.index)


def shapeOfRow (d typeCode index : ℕ) : Option Shape :=
  match typeCode with
  | 1 => some ⟨.type1, index, d⟩
  | 2 => some ⟨.type2, index, d⟩
  | 3 => some ⟨.type3, index, d⟩
  | _ => none

def rowKeyExec (d typeCode index : ℕ) : Option (ℕ × ℕ × ℕ × ℕ) :=
  (shapeOfRow d typeCode index).map shapeKeyExec

structure OfferObservation where
  innerLength : ℕ
  links : ℕ
  shortened : Bool
  gain : ℕ
  deriving DecidableEq

def observeTrace (t : OfferTrace) : OfferObservation :=
  ⟨t.block.inner.length, linkCount t.block.route, t.shortened,
    gain t.block.inner t.block.route⟩

def observeOffer (pool : List (List ℕ)) (s : ℤ) (slot : Slot) : Option OfferObservation :=
  (offerTrace pool s slot).map observeTrace

end DivisorGraphRuleH.Exec
