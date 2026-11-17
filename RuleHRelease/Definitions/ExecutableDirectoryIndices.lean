import Mathlib
import RuleHRelease.Definitions.ExecutableOffers
set_option autoImplicit false

namespace DivisorGraphRuleH.Exec


def nextPrimeExec (lower : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes lower)


def oddPrimeFast (i : ℕ) : ℕ :=
  Nat.rec 2 (fun _ previous => nextPrimeExec (previous + 1)) i

def toSlotFast (sh : Shape) : Slot :=
  match sh.kind with
  | .type1 => .type1 sh.d
  | .type2 => .type2 (oddPrimeFast (sh.index - 1)) (oddPrimeFast sh.index) sh.d
  | .type3 => .type3 sh.index sh.d

def shapeSizeFast (sh : Shape) : ℕ :=
  match sh.kind with
  | .type1 => 3 * sh.d
  | .type2 => 2 * oddPrimeFast (sh.index - 1) * sh.d
  | .type3 => 2 ^ sh.index * sh.d

def shapeKeyFast (sh : Shape) : ℕ × ℕ × ℕ × ℕ :=
  (shapeSizeFast sh, sh.d, sh.kind.code, sh.index)

def rowKeyFast (d typeCode index : ℕ) : Option (ℕ × ℕ × ℕ × ℕ) :=
  (shapeOfRow d typeCode index).map shapeKeyFast


def primesUpTo (bound : ℕ) : List ℕ :=
  (List.range (bound + 1)).filter (fun p => decide (Nat.Prime p))

end DivisorGraphRuleH.Exec
