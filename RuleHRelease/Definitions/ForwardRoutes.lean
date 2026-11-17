import Mathlib
import RuleHRelease.Definitions.IndexSpecification
set_option autoImplicit false
open DivisorGraphRuleH

theorem DivisorGraphRuleH.ForwardRoutes.case_a (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J)  :
    DivisorGraphRuleH.forwardH J 0 (DivisorGraphRuleH.lastIndex J) = some (DivisorGraphRuleH.up 0 (DivisorGraphRuleH.lastIndex J)) ∧
      DivisorGraphRuleH.ForwardRoutes.IndexSpec J 0 (DivisorGraphRuleH.lastIndex J) (DivisorGraphRuleH.up 0 (DivisorGraphRuleH.lastIndex J)) := by
  obtain ⟨hnpos, hnlen, hnb, hidx⟩ := Foundation.lastIndex_bounds J hJ
  have hv : 0 < lastIndex J ∧ lastIndex J < J.length := ⟨by omega, hnb⟩
  refine ⟨?_, ?_⟩
  · simp [forwardH, hv]
  · refine ⟨?_, (Foundation.up_endpoints 0 (lastIndex J) (by omega)).1,
      (Foundation.up_endpoints 0 (lastIndex J) (by omega)).2,
      IndexWords.up_chain J hJ 0 (lastIndex J) hnb⟩
    rw [IndexWords.up_zero_range, hnlen]

theorem DivisorGraphRuleH.ForwardRoutes.case_b (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) (hn : 1 < (DivisorGraphRuleH.lastIndex J)) :
    DivisorGraphRuleH.forwardH J 0 1 = some ([0] ++ DivisorGraphRuleH.down (DivisorGraphRuleH.lastIndex J) 1) ∧
      DivisorGraphRuleH.ForwardRoutes.IndexSpec J 0 1 ([0] ++ DivisorGraphRuleH.down (DivisorGraphRuleH.lastIndex J) 1) := by
  obtain ⟨hnpos, hnlen, hnb, hidx⟩ := Foundation.lastIndex_bounds J hJ
  have hv : 0 < 1 ∧ 1 < J.length := ⟨by omega, by omega⟩
  have hne : (1 : ℕ) ≠ lastIndex J := by omega
  have hd := Foundation.down_endpoints (lastIndex J) 1 (by omega)
  refine ⟨?_, ?_⟩
  · simp [forwardH, hv, hne]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [hnlen] using IndexWords.zero_positive_perm (down (lastIndex J) 1)
        (lastIndex J) (IndexWords.down_perm_up (lastIndex J) 1)
    · simp
    · simpa only [List.getLast?_append, hd.2, Option.or]
    · simpa only [List.nil_append] using IndexWords.zero_stitch J hJ []
        (down (lastIndex J) 1) List.isChain_nil (IndexWords.down_chain J hJ (lastIndex J) 1 hnb)

theorem DivisorGraphRuleH.ForwardRoutes.case_c (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) (w : ℕ) (hw : 1 < w) (hwn : w < (DivisorGraphRuleH.lastIndex J)) (hew : DivisorGraphRuleH.e J (w - 1)) :
    DivisorGraphRuleH.forwardH J 0 w = some (DivisorGraphRuleH.up 0 (w - 1) ++ DivisorGraphRuleH.down (DivisorGraphRuleH.lastIndex J) w) ∧
      DivisorGraphRuleH.ForwardRoutes.IndexSpec J 0 w (DivisorGraphRuleH.up 0 (w - 1) ++ DivisorGraphRuleH.down (DivisorGraphRuleH.lastIndex J) w) := by
  obtain ⟨hnpos, hnlen, hnb, hidx⟩ := Foundation.lastIndex_bounds J hJ
  have hv : 0 < w ∧ w < J.length := ⟨by omega, by omega⟩
  have hne : w ≠ lastIndex J := by omega
  have hn1 : w ≠ 1 := by omega
  have hs : w - 1 + 1 = w := by omega
  have ha := Foundation.up_endpoints 0 (w - 1) (by omega)
  have hc := Foundation.down_endpoints (lastIndex J) w (by omega)
  refine ⟨?_, ?_⟩
  · simp [forwardH, hv, hne, hn1, hew]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · have hp := IndexWords.append_blocks_perm (up 0 (w - 1)) (down (lastIndex J) w)
        0 (w - 1) (lastIndex J) (by omega) (by omega) (List.Perm.refl _)
        (by simpa only [hs] using IndexWords.down_perm_up (lastIndex J) w)
      simpa only [IndexWords.up_zero_range, hnlen] using hp
    · simpa [List.head?_append, ha.1]
    · simpa only [List.getLast?_append, hc.2, Option.or]
    · exact IndexWords.chain_append_endpoints J _ _ (w - 1) (lastIndex J)
        (IndexWords.up_chain J hJ 0 (w - 1) (by omega))
        (IndexWords.down_chain J hJ (lastIndex J) w hnb) ha.2 hc.1
        (IndexWords.even_junction J hJ (w - 1) hew).2

theorem DivisorGraphRuleH.ForwardRoutes.case_d (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) (w : ℕ) (hw : 1 < w) (hwn : w < (DivisorGraphRuleH.lastIndex J)) (hnw : ¬ DivisorGraphRuleH.e J (w - 1)) (he1 : DivisorGraphRuleH.e J 1) :
    DivisorGraphRuleH.forwardH J 0 w = some ([0] ++ DivisorGraphRuleH.down (w - 1) 1 ++ DivisorGraphRuleH.down (DivisorGraphRuleH.lastIndex J) w) ∧
      DivisorGraphRuleH.ForwardRoutes.IndexSpec J 0 w ([0] ++ DivisorGraphRuleH.down (w - 1) 1 ++ DivisorGraphRuleH.down (DivisorGraphRuleH.lastIndex J) w) := by
  obtain ⟨hnpos, hnlen, hnb, hidx⟩ := Foundation.lastIndex_bounds J hJ
  have hv : 0 < w ∧ w < J.length := ⟨by omega, by omega⟩
  have hne : w ≠ lastIndex J := by omega
  have hn1 : w ≠ 1 := by omega
  have hs : w - 1 + 1 = w := by omega
  have ha := Foundation.down_endpoints (w - 1) 1 (by omega)
  have hc := Foundation.down_endpoints (lastIndex J) w (by omega)
  refine ⟨?_, ?_⟩
  · simp [forwardH, hv, hne, hn1, hnw, he1]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · have hp := IndexWords.append_blocks_perm (down (w - 1) 1) (down (lastIndex J) w)
        1 (w - 1) (lastIndex J) (by omega) (by omega) (IndexWords.down_perm_up (w - 1) 1)
        (by simpa only [hs] using IndexWords.down_perm_up (lastIndex J) w)
      simpa only [List.append_assoc, hnlen] using
        IndexWords.zero_positive_perm _ (lastIndex J) hp
    · simp
    · simpa only [List.getLast?_append, hc.2, Option.or]
    · have hcAB := IndexWords.chain_append_endpoints J _ _ 1 (lastIndex J)
        (IndexWords.down_chain J hJ (w - 1) 1 (by omega))
        (IndexWords.down_chain J hJ (lastIndex J) w hnb) ha.2 hc.1
        (IndexWords.even_junction J hJ 1 he1).2
      simpa only [List.nil_append, List.append_assoc] using
        IndexWords.zero_stitch J hJ [] _ List.isChain_nil hcAB

theorem DivisorGraphRuleH.ForwardRoutes.case_e (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) (u : ℕ) (hu : 1 ≤ u) (hun : u < (DivisorGraphRuleH.lastIndex J)) :
    DivisorGraphRuleH.forwardH J u (DivisorGraphRuleH.lastIndex J) = some (DivisorGraphRuleH.down u 1 ++ [0] ++ DivisorGraphRuleH.up (u + 1) (DivisorGraphRuleH.lastIndex J)) ∧
      DivisorGraphRuleH.ForwardRoutes.IndexSpec J u (DivisorGraphRuleH.lastIndex J) (DivisorGraphRuleH.down u 1 ++ [0] ++ DivisorGraphRuleH.up (u + 1) (DivisorGraphRuleH.lastIndex J)) := by
  obtain ⟨hnpos, hnlen, hnb, hidx⟩ := Foundation.lastIndex_bounds J hJ
  have hv : u < lastIndex J ∧ lastIndex J < J.length := ⟨hun, hnb⟩
  have hnu : u ≠ 0 := by omega
  have ha := Foundation.down_endpoints u 1 hu
  have hc := Foundation.up_endpoints (u + 1) (lastIndex J) (by omega)
  refine ⟨?_, ?_⟩
  · simp [forwardH, hv, hnu]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [hnlen] using IndexWords.two_positive_blocks_perm (down u 1) (up (u + 1) (lastIndex J))
        u (lastIndex J) (by omega) (by omega) (IndexWords.down_perm_up u 1) (List.Perm.refl _)
    · simpa [List.head?_append, ha.1]
    · simpa only [List.getLast?_append, hc.2, Option.or]
    · exact IndexWords.zero_stitch J hJ (down u 1) (up (u + 1) (lastIndex J)) (IndexWords.down_chain J hJ u 1 (by omega)) (IndexWords.up_chain J hJ (u + 1) (lastIndex J) hnb)

theorem DivisorGraphRuleH.ForwardRoutes.case_f (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) (u : ℕ) (hu : 1 ≤ u) (hun : u + 1 < (DivisorGraphRuleH.lastIndex J)) :
    DivisorGraphRuleH.forwardH J u (u + 1) = some (DivisorGraphRuleH.down u 1 ++ [0] ++ DivisorGraphRuleH.down (DivisorGraphRuleH.lastIndex J) (u + 1)) ∧
      DivisorGraphRuleH.ForwardRoutes.IndexSpec J u (u + 1) (DivisorGraphRuleH.down u 1 ++ [0] ++ DivisorGraphRuleH.down (DivisorGraphRuleH.lastIndex J) (u + 1)) := by
  obtain ⟨hnpos, hnlen, hnb, hidx⟩ := Foundation.lastIndex_bounds J hJ
  have hv : u < u + 1 ∧ u + 1 < J.length := ⟨by omega, by omega⟩
  have hnu : u ≠ 0 := by omega
  have hnw : u + 1 ≠ lastIndex J := by omega
  have ha := Foundation.down_endpoints u 1 hu
  have hc := Foundation.down_endpoints (lastIndex J) (u + 1) (by omega)
  refine ⟨?_, ?_⟩
  · simp [forwardH, hv, hnu, hnw]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [hnlen] using IndexWords.two_positive_blocks_perm (down u 1) (down (lastIndex J) (u + 1))
        u (lastIndex J) (by omega) (by omega) (IndexWords.down_perm_up u 1) (IndexWords.down_perm_up (lastIndex J) (u + 1))
    · simpa [List.head?_append, ha.1]
    · simpa only [List.getLast?_append, hc.2, Option.or]
    · exact IndexWords.zero_stitch J hJ (down u 1) (down (lastIndex J) (u + 1)) (IndexWords.down_chain J hJ u 1 (by omega)) (IndexWords.down_chain J hJ (lastIndex J) (u + 1) hnb)

theorem DivisorGraphRuleH.ForwardRoutes.case_g (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) (w : ℕ) (hw : 2 < w) (hwn : w < (DivisorGraphRuleH.lastIndex J)) :
    DivisorGraphRuleH.forwardH J 1 w = some (DivisorGraphRuleH.up 1 (w - 1) ++ [0] ++ DivisorGraphRuleH.down (DivisorGraphRuleH.lastIndex J) w) ∧
      DivisorGraphRuleH.ForwardRoutes.IndexSpec J 1 w (DivisorGraphRuleH.up 1 (w - 1) ++ [0] ++ DivisorGraphRuleH.down (DivisorGraphRuleH.lastIndex J) w) := by
  obtain ⟨hnpos, hnlen, hnb, hidx⟩ := Foundation.lastIndex_bounds J hJ
  have hv : 1 < w ∧ w < J.length := ⟨by omega, by omega⟩
  have hnw : w ≠ lastIndex J := by omega
  have hn2 : w ≠ 1 + 1 := by omega
  have hs : w - 1 + 1 = w := by omega
  have ha := Foundation.up_endpoints 1 (w - 1) (by omega)
  have hc := Foundation.down_endpoints (lastIndex J) w (by omega)
  refine ⟨?_, ?_⟩
  · simp [forwardH, hv, hnw, hn2]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [hnlen] using IndexWords.two_positive_blocks_perm (up 1 (w - 1)) (down (lastIndex J) w)
        (w - 1) (lastIndex J) (by omega) (by omega) (List.Perm.refl _) (by simpa only [hs] using IndexWords.down_perm_up (lastIndex J) w)
    · simpa [List.head?_append, ha.1]
    · simpa only [List.getLast?_append, hc.2, Option.or]
    · exact IndexWords.zero_stitch J hJ (up 1 (w - 1)) (down (lastIndex J) w) (IndexWords.up_chain J hJ 1 (w - 1) (by omega)) (IndexWords.down_chain J hJ (lastIndex J) w hnb)

theorem DivisorGraphRuleH.ForwardRoutes.case_h (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) (u w : ℕ) (hu : 2 ≤ u) (huw : u + 1 < w) (hwn : w < (DivisorGraphRuleH.lastIndex J)) (hew : DivisorGraphRuleH.e J (w - 1)) :
    DivisorGraphRuleH.forwardH J u w = some (DivisorGraphRuleH.down u 1 ++ [0] ++ DivisorGraphRuleH.up (u + 1) (w - 1) ++ DivisorGraphRuleH.down (DivisorGraphRuleH.lastIndex J) w) ∧
      DivisorGraphRuleH.ForwardRoutes.IndexSpec J u w (DivisorGraphRuleH.down u 1 ++ [0] ++ DivisorGraphRuleH.up (u + 1) (w - 1) ++ DivisorGraphRuleH.down (DivisorGraphRuleH.lastIndex J) w) := by
  obtain ⟨hnpos, hnlen, hnb, hidx⟩ := Foundation.lastIndex_bounds J hJ
  have hv : u < w ∧ w < J.length := ⟨by omega, by omega⟩
  have hnu0 : u ≠ 0 := by omega
  have hnu1 : u ≠ 1 := by omega
  have hnwn : w ≠ lastIndex J := by omega
  have hnwa : w ≠ u + 1 := by omega
  have ha := Foundation.down_endpoints u 1 (by omega)
  have hb := Foundation.up_endpoints (u + 1) (w - 1) (by omega)
  have hc := Foundation.down_endpoints (lastIndex J) w (by omega)
  refine ⟨?_, ?_⟩
  · simp [forwardH, hv, hnu0, hnu1, hnwn, hnwa, hew]
  · refine ⟨?_, ?_, ?_, ?_⟩
    ·
      simpa only [hnlen] using IndexWords.three_positive_blocks_perm
        (down u 1) (up (u + 1) (w - 1)) (down (lastIndex J) w) u w (lastIndex J)
        (by omega) (by omega) (by omega) (IndexWords.down_perm_up u 1)
        (List.Perm.refl _) (IndexWords.down_perm_up (lastIndex J) w)
    · simpa [List.head?_append, ha.1]
    · simpa only [List.getLast?_append, hc.2, Option.or]
    · have hcAB := IndexWords.zero_stitch J hJ (down u 1) (up (u + 1) (w - 1))
        (IndexWords.down_chain J hJ u 1 (by omega)) (IndexWords.up_chain J hJ (u + 1) (w - 1) (by omega))
      have hjoin := IndexWords.chain_append_endpoints J _ _ (w - 1) (lastIndex J)
        hcAB (IndexWords.down_chain J hJ (lastIndex J) w hnb)
        (by simp only [List.getLast?_append, hb.2, Option.or]) hc.1
        (IndexWords.even_junction J hJ (w - 1) hew).2
      simpa only [List.append_assoc] using hjoin

theorem DivisorGraphRuleH.ForwardRoutes.case_i (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) (u w : ℕ) (hu : 2 ≤ u) (huw : u + 1 < w) (hwn : w < (DivisorGraphRuleH.lastIndex J)) (hnw : ¬ DivisorGraphRuleH.e J (w - 1)) (heu : DivisorGraphRuleH.e J (u + 1)) :
    DivisorGraphRuleH.forwardH J u w = some (DivisorGraphRuleH.down u 1 ++ [0] ++ DivisorGraphRuleH.down (w - 1) (u + 1) ++ DivisorGraphRuleH.down (DivisorGraphRuleH.lastIndex J) w) ∧
      DivisorGraphRuleH.ForwardRoutes.IndexSpec J u w (DivisorGraphRuleH.down u 1 ++ [0] ++ DivisorGraphRuleH.down (w - 1) (u + 1) ++ DivisorGraphRuleH.down (DivisorGraphRuleH.lastIndex J) w) := by
  obtain ⟨hnpos, hnlen, hnb, hidx⟩ := Foundation.lastIndex_bounds J hJ
  have hv : u < w ∧ w < J.length := ⟨by omega, by omega⟩
  have hnu0 : u ≠ 0 := by omega
  have hnu1 : u ≠ 1 := by omega
  have hnwn : w ≠ lastIndex J := by omega
  have hnwa : w ≠ u + 1 := by omega
  have ha := Foundation.down_endpoints u 1 (by omega)
  have hb := Foundation.down_endpoints (w - 1) (u + 1) (by omega)
  have hc := Foundation.down_endpoints (lastIndex J) w (by omega)
  refine ⟨?_, ?_⟩
  · simp [forwardH, hv, hnu0, hnu1, hnwn, hnwa, hnw, heu]
  · refine ⟨?_, ?_, ?_, ?_⟩
    ·
      simpa only [hnlen] using IndexWords.three_positive_blocks_perm
        (down u 1) (down (w - 1) (u + 1)) (down (lastIndex J) w) u w (lastIndex J)
        (by omega) (by omega) (by omega) (IndexWords.down_perm_up u 1)
        (IndexWords.down_perm_up (w - 1) (u + 1)) (IndexWords.down_perm_up (lastIndex J) w)
    · simpa [List.head?_append, ha.1]
    · simpa only [List.getLast?_append, hc.2, Option.or]
    · have hcAB := IndexWords.zero_stitch J hJ (down u 1) (down (w - 1) (u + 1))
        (IndexWords.down_chain J hJ u 1 (by omega)) (IndexWords.down_chain J hJ (w - 1) (u + 1) (by omega))
      have hjoin := IndexWords.chain_append_endpoints J _ _ (u + 1) (lastIndex J)
        hcAB (IndexWords.down_chain J hJ (lastIndex J) w hnb)
        (by simp only [List.getLast?_append, hb.2, Option.or]) hc.1
        (IndexWords.even_junction J hJ (u + 1) heu).2
      simpa only [List.append_assoc] using hjoin

theorem DivisorGraphRuleH.ForwardRoutes.case_j (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) (u w : ℕ) (hu : 2 ≤ u) (huw : u + 1 < w) (hwn : w < (DivisorGraphRuleH.lastIndex J)) (hnw : ¬ DivisorGraphRuleH.e J (w - 1)) (hnu : ¬ DivisorGraphRuleH.e J (u + 1)) (heu : DivisorGraphRuleH.e J (u - 1)) :
    DivisorGraphRuleH.forwardH J u w = some (DivisorGraphRuleH.up u (w - 1) ++ [0] ++ DivisorGraphRuleH.up 1 (u - 1) ++ DivisorGraphRuleH.down (DivisorGraphRuleH.lastIndex J) w) ∧
      DivisorGraphRuleH.ForwardRoutes.IndexSpec J u w (DivisorGraphRuleH.up u (w - 1) ++ [0] ++ DivisorGraphRuleH.up 1 (u - 1) ++ DivisorGraphRuleH.down (DivisorGraphRuleH.lastIndex J) w) := by
  obtain ⟨hnpos, hnlen, hnb, hidx⟩ := Foundation.lastIndex_bounds J hJ
  have hv : u < w ∧ w < J.length := ⟨by omega, by omega⟩
  have hnu0 : u ≠ 0 := by omega
  have hnu1 : u ≠ 1 := by omega
  have hnwn : w ≠ lastIndex J := by omega
  have hnwa : w ≠ u + 1 := by omega
  have ha := Foundation.up_endpoints u (w - 1) (by omega)
  have hb := Foundation.up_endpoints 1 (u - 1) (by omega)
  have hc := Foundation.down_endpoints (lastIndex J) w (by omega)
  refine ⟨?_, ?_⟩
  · simp [forwardH, hv, hnu0, hnu1, hnwn, hnwa, hnw, hnu, heu]
  · refine ⟨?_, ?_, ?_, ?_⟩
    ·
      have hsu : u - 1 + 1 = u := by omega
      have hp := IndexWords.three_positive_blocks_perm
        (up 1 (u - 1)) (up u (w - 1)) (down (lastIndex J) w) (u - 1) w (lastIndex J)
        (by omega) (by omega) (by omega) (List.Perm.refl _)
        (by simpa only [hsu] using List.Perm.refl (up u (w - 1)))
        (IndexWords.down_perm_up (lastIndex J) w)
      have hswap : (up u (w - 1) ++ [0] ++ up 1 (u - 1) ++ down (lastIndex J) w).Perm
          (up 1 (u - 1) ++ [0] ++ up u (w - 1) ++ down (lastIndex J) w) := by
        apply List.perm_iff_count.mpr
        intro x
        simp only [List.count_append]
        omega
      exact hswap.trans (by simpa only [hnlen] using hp)
    · simpa [List.head?_append, ha.1]
    · simpa only [List.getLast?_append, hc.2, Option.or]
    · have hcAB := IndexWords.zero_stitch J hJ (up u (w - 1)) (up 1 (u - 1))
        (IndexWords.up_chain J hJ u (w - 1) (by omega)) (IndexWords.up_chain J hJ 1 (u - 1) (by omega))
      have hjoin := IndexWords.chain_append_endpoints J _ _ (u - 1) (lastIndex J)
        hcAB (IndexWords.down_chain J hJ (lastIndex J) w hnb)
        (by simp only [List.getLast?_append, hb.2, Option.or]) hc.1
        (IndexWords.even_junction J hJ (u - 1) heu).2
      simpa only [List.append_assoc] using hjoin

theorem DivisorGraphRuleH.ForwardRoutes.case_k (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) (u w : ℕ) (hu : 2 ≤ u) (huw : u + 1 < w) (hwn : w < (DivisorGraphRuleH.lastIndex J)) (hnw : ¬ DivisorGraphRuleH.e J (w - 1)) (hnu : ¬ DivisorGraphRuleH.e J (u + 1)) (hnp : ¬ DivisorGraphRuleH.e J (u - 1)) (he1 : DivisorGraphRuleH.e J 1) :
    DivisorGraphRuleH.forwardH J u w = some (DivisorGraphRuleH.up u (w - 1) ++ [0] ++ DivisorGraphRuleH.down (u - 1) 1 ++ DivisorGraphRuleH.down (DivisorGraphRuleH.lastIndex J) w) ∧
      DivisorGraphRuleH.ForwardRoutes.IndexSpec J u w (DivisorGraphRuleH.up u (w - 1) ++ [0] ++ DivisorGraphRuleH.down (u - 1) 1 ++ DivisorGraphRuleH.down (DivisorGraphRuleH.lastIndex J) w) := by
  obtain ⟨hnpos, hnlen, hnb, hidx⟩ := Foundation.lastIndex_bounds J hJ
  have hv : u < w ∧ w < J.length := ⟨by omega, by omega⟩
  have hnu0 : u ≠ 0 := by omega
  have hnu1 : u ≠ 1 := by omega
  have hnwn : w ≠ lastIndex J := by omega
  have hnwa : w ≠ u + 1 := by omega
  have ha := Foundation.up_endpoints u (w - 1) (by omega)
  have hb := Foundation.down_endpoints (u - 1) 1 (by omega)
  have hc := Foundation.down_endpoints (lastIndex J) w (by omega)
  refine ⟨?_, ?_⟩
  · simp [forwardH, hv, hnu0, hnu1, hnwn, hnwa, hnw, hnu, hnp, he1]
  · refine ⟨?_, ?_, ?_, ?_⟩
    ·
      have hsu : u - 1 + 1 = u := by omega
      have hp := IndexWords.three_positive_blocks_perm
        (down (u - 1) 1) (up u (w - 1)) (down (lastIndex J) w) (u - 1) w (lastIndex J)
        (by omega) (by omega) (by omega) (IndexWords.down_perm_up (u - 1) 1)
        (by simpa only [hsu] using List.Perm.refl (up u (w - 1)))
        (IndexWords.down_perm_up (lastIndex J) w)
      have hswap : (up u (w - 1) ++ [0] ++ down (u - 1) 1 ++ down (lastIndex J) w).Perm
          (down (u - 1) 1 ++ [0] ++ up u (w - 1) ++ down (lastIndex J) w) := by
        apply List.perm_iff_count.mpr
        intro x
        simp only [List.count_append]
        omega
      exact hswap.trans (by simpa only [hnlen] using hp)
    · simpa [List.head?_append, ha.1]
    · simpa only [List.getLast?_append, hc.2, Option.or]
    · have hcAB := IndexWords.zero_stitch J hJ (up u (w - 1)) (down (u - 1) 1)
        (IndexWords.up_chain J hJ u (w - 1) (by omega)) (IndexWords.down_chain J hJ (u - 1) 1 (by omega))
      have hjoin := IndexWords.chain_append_endpoints J _ _ (1) (lastIndex J)
        hcAB (IndexWords.down_chain J hJ (lastIndex J) w hnb)
        (by simp only [List.getLast?_append, hb.2, Option.or]) hc.1
        (IndexWords.even_junction J hJ (1) he1).2
      simpa only [List.append_assoc] using hjoin

theorem DivisorGraphRuleH.ForwardRoutes.forwardH_spec (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) (u w : ℕ) (W : List ℕ)
    (h : DivisorGraphRuleH.forwardH J u w = some W) :
    DivisorGraphRuleH.ForwardRoutes.IndexSpec J u w W := by
  obtain ⟨hnpos, hnlen, hnb, hidx⟩ := Foundation.lastIndex_bounds J hJ
  have hv : u < w ∧ w < J.length := by
    by_contra hv
    simp [forwardH, hv] at h
  have hwn : w ≤ lastIndex J := (hidx w).mp hv.2
  have transfer : ∀ V : List ℕ,
      (forwardH J u w = some V ∧ ForwardRoutes.IndexSpec J u w V) → ForwardRoutes.IndexSpec J u w W := by
    intro V hs
    have hVW : V = W := Option.some.inj (hs.1.symm.trans h)
    simpa only [hVW] using hs.2
  by_cases hu0 : u = 0
  · subst u
    by_cases hwn' : w = lastIndex J
    · subst w
      exact transfer _ (ForwardRoutes.case_a J hJ)
    · by_cases hw1 : w = 1
      · subst w
        exact transfer _ (ForwardRoutes.case_b J hJ (by omega))
      · by_cases hew : e J (w - 1)
        · exact transfer _ (ForwardRoutes.case_c J hJ w (by omega) (by omega) hew)
        · by_cases he1 : e J 1
          · exact transfer _ (ForwardRoutes.case_d J hJ w (by omega) (by omega) hew he1)
          · simp [forwardH, hv, hwn', hw1, hew, he1] at h
  · by_cases hwn' : w = lastIndex J
    · subst w
      exact transfer _ (ForwardRoutes.case_e J hJ u (by omega) hv.1)
    · by_cases hwa : w = u + 1
      · subst w
        exact transfer _ (ForwardRoutes.case_f J hJ u (by omega) (by omega))
      · by_cases hu1 : u = 1
        · subst u
          exact transfer _ (ForwardRoutes.case_g J hJ w (by omega) (by omega))
        · by_cases hew : e J (w - 1)
          · exact transfer _ (ForwardRoutes.case_h J hJ u w (by omega) (by omega) (by omega) hew)
          · by_cases heu : e J (u + 1)
            · exact transfer _ (ForwardRoutes.case_i J hJ u w (by omega) (by omega) (by omega) hew heu)
            · by_cases hep : e J (u - 1)
              · exact transfer _ (ForwardRoutes.case_j J hJ u w (by omega) (by omega) (by omega) hew heu hep)
              · by_cases he1 : e J 1
                · exact transfer _ (ForwardRoutes.case_k J hJ u w (by omega) (by omega) (by omega) hew heu hep he1)
                · simp [forwardH, hv, hu0, hwn', hwa, hu1, hew, heu, hep, he1] at h

def DivisorGraphRuleH.ForwardRoutes.results : Unit := ()
