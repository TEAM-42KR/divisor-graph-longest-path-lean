import Mathlib
import RuleHRelease.Definitions.ForwardRoutes
set_option autoImplicit false

theorem DivisorGraphRuleH.Feasibility.feasible_of_even_one (J : List ℕ)
    (he : DivisorGraphRuleH.e J 1) (u w : ℕ)
    (hu : u < J.length) (hw : w < J.length) (hne : u ≠ w) :
    DivisorGraphRuleH.Feasible J u w := by
  have forward (a b : ℕ) (hab : a < b) (hb : b < J.length) :
      (DivisorGraphRuleH.forwardH J a b).isSome = true := by
    simp only [DivisorGraphRuleH.forwardH, hab, hb, he, and_self,
      not_true_eq_false, if_false, if_true]
    split_ifs <;> rfl
  rcases lt_or_gt_of_ne hne with huw | hwu
  · simpa only [DivisorGraphRuleH.Feasible, DivisorGraphRuleH.H, if_pos huw] using
      forward u w huw hw
  · simpa only [DivisorGraphRuleH.Feasible, DivisorGraphRuleH.H,
      if_neg (not_lt_of_ge hwu.le), if_pos hwu, Option.isSome_map] using
      forward w u hwu hu


theorem DivisorGraphRuleH.Feasibility.universal_feasibility (J : List ℕ) (s : ℤ)
    (hJ : DivisorGraphRuleH.TablePathAt J s) (he : DivisorGraphRuleH.e J 1) :
    ∀ u w : ℕ, u < J.length → w < J.length → u ≠ w → DivisorGraphRuleH.Feasible J u w := by
  intro u w hu hw hne
  exact DivisorGraphRuleH.Feasibility.feasible_of_even_one J he u w hu hw hne


def DivisorGraphRuleH.Feasibility.results : Unit := ()
