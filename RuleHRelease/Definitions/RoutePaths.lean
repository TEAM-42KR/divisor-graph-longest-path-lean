import Mathlib
import RuleHRelease.Definitions.ForwardRoutes
set_option autoImplicit false
open DivisorGraphRuleH

theorem DivisorGraphRuleH.RoutePaths.indexSpec_reverse (J : List ℕ) (u w : ℕ) (W : List ℕ)
    (hW : DivisorGraphRuleH.ForwardRoutes.IndexSpec J u w W) :
    DivisorGraphRuleH.ForwardRoutes.IndexSpec J w u W.reverse := by
  rcases hW with ⟨hp, hh, hl, hc⟩
  exact ⟨(List.reverse_perm W).trans hp,
    by simpa only [List.head?_reverse] using hl,
    by simpa only [List.getLast?_reverse] using hh,
    IndexWords.reverse_chain J W hc⟩

theorem DivisorGraphRuleH.RoutePaths.routeIndices_spec (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) (u w : ℕ)
    (hfeasible : DivisorGraphRuleH.Feasible J u w) :
    DivisorGraphRuleH.ForwardRoutes.IndexSpec J u w (DivisorGraphRuleH.routeIndices J u w) := by
  cases hH : H J u w with
  | none => simp [Feasible, hH] at hfeasible
  | some W =>
    have hspec : ForwardRoutes.IndexSpec J u w W := by
      unfold H at hH
      split_ifs at hH with huw hwu
      · exact ForwardRoutes.forwardH_spec J hJ u w W hH
      · cases hf : forwardH J w u with
        | none => simp [hf] at hH
        | some V =>
          have hrev : V.reverse = W := by
            simpa only [hf, Option.map_some, Option.some.injEq] using hH
          subst W
          exact RoutePaths.indexSpec_reverse J w u V (ForwardRoutes.forwardH_spec J hJ w u V hf)
    simpa only [routeIndices, hH, Option.getD_some] using hspec

theorem DivisorGraphRuleH.RoutePaths.map_indexSpec (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) (u w : ℕ) (W : List ℕ)
    (hW : DivisorGraphRuleH.ForwardRoutes.IndexSpec J u w W) :
    DivisorGraphRuleH.DivisorPath (W.map (DivisorGraphRuleH.term J)) ∧
    (W.map (DivisorGraphRuleH.term J)).head? = some (DivisorGraphRuleH.term J u) ∧
    (W.map (DivisorGraphRuleH.term J)).getLast? = some (DivisorGraphRuleH.term J w) ∧
    (W.map (DivisorGraphRuleH.term J)).Perm J := by
  rcases hW with ⟨hp, hh, hl, hc⟩
  have hmap : (W.map (term J)).Perm J := by
    simpa only [Foundation.term_map_range] using hp.map (term J)
  refine ⟨⟨?_, hmap.nodup_iff.mpr hJ.1.2.1,
      (List.isChain_map (term J)).mpr hc⟩, ?_, ?_, hmap⟩
  · intro t ht
    exact hJ.1.1 t (hmap.mem_iff.mp ht)
  · simp only [List.head?_map, hh, Option.map_some]
  · simp only [List.getLast?_map, hl, Option.map_some]

theorem DivisorGraphRuleH.H1 (J : List ℕ) (s : ℤ) (hJ : TablePathAt J s)
    (u w : ℕ) (hu : u < J.length) (hw : w < J.length)
    (hne : u ≠ w) (hfeasible : Feasible J u w) :
    (routeIndices J u w).Perm (List.range J.length) ∧
    (routeIndices J u w).head? = some u ∧
    (routeIndices J u w).getLast? = some w ∧
    (routeIndices J u w).IsChain (fun i i' => Comparable (term J i) (term J i')) ∧
    DivisorPath (routeOrder J u w) ∧
    (routeOrder J u w).head? = some (term J u) ∧
    (routeOrder J u w).getLast? = some (term J w) ∧
    (routeOrder J u w).Perm J := by
  have hI := RoutePaths.routeIndices_spec J hJ.1 u w hfeasible
  have hP := RoutePaths.map_indexSpec J hJ.1 u w (routeIndices J u w) hI
  exact ⟨hI.1, hI.2.1, hI.2.2.1, hI.2.2.2, hP⟩

def DivisorGraphRuleH.RoutePaths.results : Unit := ()
