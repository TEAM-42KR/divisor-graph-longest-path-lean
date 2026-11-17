import Mathlib
import RuleHRelease.Definitions.IndexWords
set_option autoImplicit false

def DivisorGraphRuleH.ForwardRoutes.IndexSpec (J : List ℕ) (u w : ℕ) (W : List ℕ) : Prop :=
  W.Perm (List.range J.length) ∧ W.head? = some u ∧ W.getLast? = some w ∧
    W.IsChain (fun i j => DivisorGraphRuleH.Comparable
      (DivisorGraphRuleH.term J i) (DivisorGraphRuleH.term J j))
