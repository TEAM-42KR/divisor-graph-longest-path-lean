import Mathlib
import RuleHRelease.Definitions.Arithmetic
import RuleHRelease.Definitions.RoutePaths
set_option autoImplicit false

def DivisorGraphRuleH.OrderedSearch.validityAPI : Prop := True

def DivisorGraphRuleH.OrderedSearch.LinkValid (J : List ℕ) (s : ℤ) (m i x : ℕ) : Prop :=
  0 < x ∧ (x : ℤ) ≤ s ∧ x ∉ J ∧ m ∣ x ∧
  DivisorGraphRuleH.term J i ∣ x ∧
  (i = DivisorGraphRuleH.lastIndex J → Even x ∧ 4 ≤ x) ∧
  (i = 0 → 2 ≤ m)

def DivisorGraphRuleH.OrderedSearch.SideValid (J : List ℕ) (s : ℤ) (m i : ℕ)
    (link : Option ℕ) : Prop :=
  (∀ x, link = some x → DivisorGraphRuleH.OrderedSearch.LinkValid J s m i x) ∧
  (link = none → m ∣ DivisorGraphRuleH.term J i)

def DivisorGraphRuleH.OrderedSearch.OptionValid (J : List ℕ) (s : ℤ) (m : ℕ)
    (A : DivisorGraphRuleH.EndpointOption) : Prop :=
  (A.index = 0 ∨ A.index = DivisorGraphRuleH.lastIndex J) ∧ A.index < J.length ∧
  match A.links with
  | none => m ∣ DivisorGraphRuleH.term J A.index
  | some xs => xs ≠ [] ∧ ∀ x ∈ xs, DivisorGraphRuleH.OrderedSearch.LinkValid J s m A.index x

def DivisorGraphRuleH.OrderedSearch.CandidateValid (J : List ℕ) (s : ℤ)
    (slot : DivisorGraphRuleH.Slot) (r : DivisorGraphRuleH.Route) : Prop :=
  DivisorGraphRuleH.IsRoute J r ∧
  DivisorGraphRuleH.OrderedSearch.SideValid J s slot.a r.u r.x ∧
  DivisorGraphRuleH.OrderedSearch.SideValid J s slot.a' r.w r.y ∧
  (∀ x y, r.x = some x → r.y = some y → x ≠ y)
