import Mathlib
import RuleHRelease.Definitions.OrderedSearch
import RuleHRelease.Definitions.Feasibility
set_option autoImplicit false

open DivisorGraphRuleH

def DivisorGraphRuleH.RouteExistence.results : Prop := True

theorem DivisorGraphRuleH.RouteExistence.interior_of_mem (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) (m x : ℕ)
    (hx : x ∈ J) (hx1 : x ≠ 1) (hx2 : x ≠ 2) (hd : m ∣ x) :
    ∃ i, i ∈ DivisorGraphRuleH.interiorIndices J m ∧ i < J.length ∧
      DivisorGraphRuleH.term J i = x := by
  obtain ⟨i, hi, ht⟩ := Foundation.term_index_of_mem J x hx
  have hb := Foundation.lastIndex_bounds J hJ
  have hi0 : i ≠ 0 := by
    intro hz
    apply hx1
    rw [← ht, hz, Foundation.term_first J hJ]
  have hin : i ≠ lastIndex J := by
    intro hz
    apply hx2
    rw [← ht, hz, Foundation.term_last J hJ]
  refine ⟨i, (OrderedSearch.mem_interiorIndices_iff J m i).mpr ⟨?_, ?_, ?_⟩, hi, ht⟩
  · omega
  · have hil := (hb.2.2.2 i).mp hi
    omega
  · rw [ht]
    exact hd

theorem DivisorGraphRuleH.RouteExistence.free_self (J : List ℕ) (s : ℤ) (m : ℕ) (hm : (m : ℤ) ≤ s) (hx : m ∉ J) :
    m ∈ DivisorGraphRuleH.freeMultiples J s m := by
  exact (OrderedSearch.mem_freeMultiples_iff J s m m).mpr ⟨le_rfl, dvd_refl m, hm, hx⟩

theorem DivisorGraphRuleH.RouteExistence.nolink_pair (J : List ℕ) (s : ℤ) (slot : DivisorGraphRuleH.Slot) (u w : ℕ)
    (hu : u ∈ DivisorGraphRuleH.noLinkStarts J s slot)
    (hw : w ∈ DivisorGraphRuleH.noLinkEnds J s slot)
    (hne : u ≠ w) (hf : DivisorGraphRuleH.Feasible J u w) :
    ∃ r, DivisorGraphRuleH.SearchReturns J s slot r := by
  apply OrderedSearch.search_of_mem_kind J s slot .R5 ⟨none, u, w, none⟩
  exact (OrderedSearch.mem_R5_iff J s slot _).mpr ⟨u, hu, w, hw, hne, hf, rfl⟩

theorem DivisorGraphRuleH.RouteExistence.linked_nolink (J : List ℕ) (s : ℤ) (slot : DivisorGraphRuleH.Slot)
    (A : DivisorGraphRuleH.EndpointOption) (xs : List ℕ) (w : ℕ)
    (hA : A ∈ DivisorGraphRuleH.startOptions J s slot)
    (hlinks : A.links = some xs) (hxs : xs ≠ [])
    (hw : w ∈ DivisorGraphRuleH.noLinkEnds J s slot)
    (hne : A.index ≠ w) (hf : DivisorGraphRuleH.Feasible J A.index w) :
    ∃ r, DivisorGraphRuleH.SearchReturns J s slot r := by
  obtain ⟨x, hhead⟩ : ∃ x, xs.head? = some x := by
    cases xs with
    | nil => exact False.elim (hxs rfl)
    | cons x xs => exact ⟨x, rfl⟩
  unfold noLinkEnds at hw
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨B, hB, hfilter⟩ := List.mem_filterMap.mp hw
    cases hl : B.links with
    | none =>
      have hidx : B.index = w := by simpa [hl] using hfilter
      apply OrderedSearch.search_of_mem_kind J s slot .R2 ⟨some x, A.index, B.index, none⟩
      exact (OrderedSearch.mem_R2_iff J s slot _).mpr
        ⟨A, hA, B, hB, by simpa only [hidx] using hne,
          Or.inl ⟨xs, x, hlinks, hl, hhead, rfl⟩⟩
    | some ys => simp [hl] at hfilter
  · apply OrderedSearch.search_of_mem_kind J s slot .R3 ⟨some x, A.index, w, none⟩
    exact (OrderedSearch.mem_R3_iff J s slot _).mpr
      ⟨A, hA, xs, w, x, hlinks, hw, hf, hhead, rfl⟩

theorem DivisorGraphRuleH.RouteExistence.nolink_linked (J : List ℕ) (s : ℤ) (slot : DivisorGraphRuleH.Slot)
    (u : ℕ) (B : DivisorGraphRuleH.EndpointOption) (ys : List ℕ)
    (hu : u ∈ DivisorGraphRuleH.noLinkStarts J s slot)
    (hB : B ∈ DivisorGraphRuleH.endOptions J s slot)
    (hlinks : B.links = some ys) (hys : ys ≠ [])
    (hne : u ≠ B.index) (hf : DivisorGraphRuleH.Feasible J u B.index) :
    ∃ r, DivisorGraphRuleH.SearchReturns J s slot r := by
  obtain ⟨y, hhead⟩ : ∃ y, ys.head? = some y := by
    cases ys with
    | nil => exact False.elim (hys rfl)
    | cons y ys => exact ⟨y, rfl⟩
  unfold noLinkStarts at hu
  rcases List.mem_append.mp hu with hu | hu
  · obtain ⟨A, hA, hfilter⟩ := List.mem_filterMap.mp hu
    cases hl : A.links with
    | none =>
      have hidx : A.index = u := by simpa [hl] using hfilter
      apply OrderedSearch.search_of_mem_kind J s slot .R2 ⟨none, A.index, B.index, some y⟩
      exact (OrderedSearch.mem_R2_iff J s slot _).mpr
        ⟨A, hA, B, hB, by simpa only [hidx] using hne,
          Or.inr ⟨ys, y, hl, hlinks, hhead, rfl⟩⟩
    | some xs => simp [hl] at hfilter
  · apply OrderedSearch.search_of_mem_kind J s slot .R4 ⟨none, u, B.index, some y⟩
    exact (OrderedSearch.mem_R4_iff J s slot _).mpr
      ⟨u, hu, B, hB, ys, y, hlinks, hf, hhead, rfl⟩

theorem DivisorGraphRuleH.RouteExistence.linked_pair (J : List ℕ) (s : ℤ) (slot : DivisorGraphRuleH.Slot)
    (A B : DivisorGraphRuleH.EndpointOption) (xs ys : List ℕ) (y : ℕ)
    (hA : A ∈ DivisorGraphRuleH.startOptions J s slot)
    (hB : B ∈ DivisorGraphRuleH.endOptions J s slot)
    (hAlinks : A.links = some xs) (hBlinks : B.links = some ys)
    (hxs : xs ≠ []) (hy : y ∈ ys) (hsep : ∀ x ∈ xs, x ≠ y)
    (hne : A.index ≠ B.index) : ∃ r, DivisorGraphRuleH.SearchReturns J s slot r := by
  obtain ⟨x, hhead⟩ : ∃ x, xs.head? = some x := by
    cases xs with
    | nil => exact False.elim (hxs rfl)
    | cons x xs => exact ⟨x, rfl⟩
  have hxy : x ≠ y := hsep x (List.mem_of_head? hhead)
  cases hfind : ys.find? (fun z => decide (z ≠ x)) with
  | none =>
    have hfalse := (List.find?_eq_none.mp hfind) y hy
    simp only [decide_eq_true_eq] at hfalse
    exact False.elim (hfalse hxy.symm)
  | some z =>
    apply OrderedSearch.search_of_mem_kind J s slot .R1 ⟨some x, A.index, B.index, some z⟩
    exact (OrderedSearch.mem_R1_iff J s slot _).mpr
      ⟨A, hA, B, hB, hne, xs, ys, x, z, hAlinks, hBlinks, hhead, hfind, rfl⟩

theorem DivisorGraphRuleH.RouteExistence.lcm_not_dvd_aprime (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) :
    ¬ Nat.lcm 2 slot.a ∣ slot.a' := by
  intro hd
  rcases Nat.even_or_odd slot.a with ha | ha
  · rw [Arithmetic.even_a_lcm slot hv ha] at hd
    exact Arithmetic.even_a_not_dvd_aprime slot hv ha hd
  · have hp : Odd slot.a' := by
      rw [(Arithmetic.odd_a_moduli slot hv ha).1]
      exact (by decide : Odd (3 : ℕ)).mul ha
    exact hp.not_two_dvd_nat (dvd_trans (Nat.dvd_lcm_left 2 slot.a) hd)

theorem DivisorGraphRuleH.RouteExistence.end_present (J : List ℕ) (s : ℤ) (hJ : DivisorGraphRuleH.TablePath J)
    (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) (hp : slot.a' ∈ J) :
    ∃ w, w ∈ DivisorGraphRuleH.noLinkEnds J s slot ∧ w < J.length ∧
      DivisorGraphRuleH.term J w = slot.a' ∧ w ≠ 0 := by
  have hb := Foundation.lastIndex_bounds J hJ
  by_cases hp2 : slot.a' = 2
  · have hd : slot.a' ∣ 2 := by rw [hp2]
    have hB3 : B3 J s slot = some ⟨lastIndex J, none⟩ := by simp [B3, hd]
    have hB : (⟨lastIndex J, none⟩ : EndpointOption) ∈ endOptions J s slot := by
      unfold endOptions
      exact List.mem_filterMap.mpr ⟨some ⟨lastIndex J, none⟩, by simp [hB3], rfl⟩
    refine ⟨lastIndex J, ?_, hb.2.2.1, ?_, ?_⟩
    · unfold noLinkEnds
      exact List.mem_append.mpr (Or.inl
        (List.mem_filterMap.mpr ⟨⟨lastIndex J, none⟩, hB, by simp⟩))
    · rw [Foundation.term_last J hJ, hp2]
    · omega
  · have hp1 : slot.a' ≠ 1 := by have := Arithmetic.two_le_aprime slot hv; omega
    obtain ⟨w, hw, hwlt, ht⟩ := RouteExistence.interior_of_mem J hJ slot.a' slot.a' hp hp1 hp2 (dvd_refl _)
    refine ⟨w, ?_, hwlt, ht, ?_⟩
    · unfold noLinkEnds
      exact List.mem_append.mpr (Or.inr hw)
    · have hw1 := ((OrderedSearch.mem_interiorIndices_iff J slot.a' w).mp hw).1
      omega

theorem DivisorGraphRuleH.RouteExistence.exists_route (J : List ℕ) (s : ℤ) (hJ : DivisorGraphRuleH.TablePathAt J s)
    (he : DivisorGraphRuleH.e J 1) (slot : DivisorGraphRuleH.Slot)
    (hv : slot.Valid) (hsize : (slot.size : ℤ) ≤ s) :
    ∃ r, DivisorGraphRuleH.SearchReturns J s slot r := by
  have hb := Foundation.lastIndex_bounds J hJ.1
  have hz : 0 < J.length := lt_of_lt_of_le (by decide : 0 < 2) (Foundation.tablePath_length J hJ.1)
  have hn0 : lastIndex J ≠ 0 := by omega
  have hap2 := Arithmetic.two_le_aprime slot hv
  have ha2ne := Arithmetic.a_ne_two slot hv
  have ha_bound : (slot.a : ℤ) ≤ s := by
    exact le_trans (by exact_mod_cast Arithmetic.a_le_size slot hv) hsize
  have hap_bound : (slot.a' : ℤ) ≤ s := by
    exact le_trans (by exact_mod_cast Arithmetic.aprime_le_size slot hv) hsize
  have hf := Feasibility.universal_feasibility J s hJ he
  by_cases hap : slot.a' ∈ J
  · obtain ⟨w, hw, hwlt, htw, hw0⟩ := RouteExistence.end_present J s hJ.1 slot hv hap
    by_cases ha1 : slot.a = 1
    · have hA3 : A3 J s slot = some ⟨0, none⟩ := by simp [A3, ha1]
      have hA : (⟨0, none⟩ : EndpointOption) ∈ startOptions J s slot := by
        unfold startOptions
        exact List.mem_filterMap.mpr ⟨some ⟨0, none⟩, by simp [hA3], rfl⟩
      have hu : 0 ∈ noLinkStarts J s slot := by
        unfold noLinkStarts
        exact List.mem_append.mpr (Or.inl
          (List.mem_filterMap.mpr ⟨⟨0, none⟩, hA, by simp⟩))
      exact RouteExistence.nolink_pair J s slot 0 w hu hw hw0.symm (hf 0 w hz hwlt hw0.symm)
    · by_cases ha : slot.a ∈ J
      · obtain ⟨u, hu, hult, htu⟩ :=
          RouteExistence.interior_of_mem J hJ.1 slot.a slot.a ha ha1 ha2ne (dvd_refl _)
        have hus : u ∈ noLinkStarts J s slot := by
          unfold noLinkStarts
          exact List.mem_append.mpr (Or.inr hu)
        have hne : u ≠ w := by
          intro heq
          apply Arithmetic.a_ne_aprime slot hv
          exact htu.symm.trans ((congrArg (term J) heq).trans htw)
        exact RouteExistence.nolink_pair J s slot u w hus hw hne (hf u w hult hwlt hne)
      · have hfree := RouteExistence.free_self J s slot.a ha_bound ha
        have hxs : freeMultiples J s slot.a ≠ [] := by
          intro hnil
          simpa only [hnil, List.not_mem_nil] using hfree
        have ha2 : 2 ≤ slot.a := le_trans (by decide : 2 ≤ 3) (Arithmetic.three_le_a_of_ne_one slot hv ha1)
        have hA3 : A3 J s slot = some ⟨0, some (freeMultiples J s slot.a)⟩ := by
          simp [A3, ha1, ha2, hxs]
        have hA : (⟨0, some (freeMultiples J s slot.a)⟩ : EndpointOption) ∈ startOptions J s slot := by
          unfold startOptions
          exact List.mem_filterMap.mpr
            ⟨some ⟨0, some (freeMultiples J s slot.a)⟩, by simp [hA3], rfl⟩
        exact RouteExistence.linked_nolink J s slot ⟨0, some (freeMultiples J s slot.a)⟩
          (freeMultiples J s slot.a) w hA rfl hxs hw hw0.symm (hf 0 w hz hwlt hw0.symm)
  · have hy := RouteExistence.free_self J s slot.a' hap_bound hap
    have hys : freeMultiples J s slot.a' ≠ [] := by
      intro hnil
      simpa only [hnil, List.not_mem_nil] using hy
    have hB1 : B1 J s slot = some ⟨0, some (freeMultiples J s slot.a')⟩ := by simp [B1, hys]
    have hB : (⟨0, some (freeMultiples J s slot.a')⟩ : EndpointOption) ∈ endOptions J s slot := by
      unfold endOptions
      exact List.mem_filterMap.mpr
        ⟨some ⟨0, some (freeMultiples J s slot.a')⟩, by simp [hB1], rfl⟩
    by_cases ha1 : slot.a = 1
    · have had : slot.a ∣ 2 := (Arithmetic.a_dvd_two_iff slot hv).mpr ha1
      have hA2 : A2 J s slot = some ⟨lastIndex J, none⟩ := by simp [A2, had]
      have hA : (⟨lastIndex J, none⟩ : EndpointOption) ∈ startOptions J s slot := by
        unfold startOptions
        exact List.mem_filterMap.mpr ⟨some ⟨lastIndex J, none⟩, by simp [hA2], rfl⟩
      have hus : lastIndex J ∈ noLinkStarts J s slot := by
        unfold noLinkStarts
        exact List.mem_append.mpr (Or.inl
          (List.mem_filterMap.mpr ⟨⟨lastIndex J, none⟩, hA, by simp⟩))
      exact RouteExistence.nolink_linked J s slot (lastIndex J) ⟨0, some (freeMultiples J s slot.a')⟩
        (freeMultiples J s slot.a') hus hB rfl hys hn0 (hf _ _ hb.2.2.1 hz hn0)
    · by_cases ha : slot.a ∈ J
      · obtain ⟨u, hu, hult, htu⟩ :=
          RouteExistence.interior_of_mem J hJ.1 slot.a slot.a ha ha1 ha2ne (dvd_refl _)
        have hus : u ∈ noLinkStarts J s slot := by
          unfold noLinkStarts
          exact List.mem_append.mpr (Or.inr hu)
        have hu0 : u ≠ 0 := by
          have := ((OrderedSearch.mem_interiorIndices_iff J slot.a u).mp hu).1
          omega
        exact RouteExistence.nolink_linked J s slot u ⟨0, some (freeMultiples J s slot.a')⟩
          (freeMultiples J s slot.a') hus hB rfl hys hu0 (hf _ _ hult hz hu0)
      · have from_A1 (hxs : freeMultiples J s (Nat.lcm 2 slot.a) ≠ []) :
            ∃ r, SearchReturns J s slot r := by
          have hA1 : A1 J s slot = some ⟨lastIndex J, some (freeMultiples J s (Nat.lcm 2 slot.a))⟩ := by
            simp [A1, hxs]
          have hA : (⟨lastIndex J, some (freeMultiples J s (Nat.lcm 2 slot.a))⟩ : EndpointOption)
              ∈ startOptions J s slot := by
            unfold startOptions
            exact List.mem_filterMap.mpr
              ⟨some ⟨lastIndex J, some (freeMultiples J s (Nat.lcm 2 slot.a))⟩, by simp [hA1], rfl⟩
          apply RouteExistence.linked_pair J s slot
            ⟨lastIndex J, some (freeMultiples J s (Nat.lcm 2 slot.a))⟩
            ⟨0, some (freeMultiples J s slot.a')⟩
            (freeMultiples J s (Nat.lcm 2 slot.a)) (freeMultiples J s slot.a') slot.a'
            hA hB rfl rfl hxs hy ?_ hn0
          intro x hx heq
          have hd := ((OrderedSearch.mem_freeMultiples_iff J s (Nat.lcm 2 slot.a) x).mp hx).2.1
          rw [heq] at hd
          exact RouteExistence.lcm_not_dvd_aprime slot hv hd
        rcases Nat.even_or_odd slot.a with hae | hao
        · apply from_A1
          have hx : slot.a ∈ freeMultiples J s (Nat.lcm 2 slot.a) := by
            rw [Arithmetic.even_a_lcm slot hv hae]
            exact RouteExistence.free_self J s slot.a ha_bound ha
          intro hnil
          simpa only [hnil, List.not_mem_nil] using hx
        · have hd := Arithmetic.odd_a_double_interior_bounds slot hv hao ha1
          by_cases hx : 2 * slot.a ∈ J
          · obtain ⟨u, hu, hult, htu⟩ :=
              RouteExistence.interior_of_mem J hJ.1 slot.a (2 * slot.a) hx hd.2.1 hd.2.2.1 hd.2.2.2.2.1
            have hus : u ∈ noLinkStarts J s slot := by
              unfold noLinkStarts
              exact List.mem_append.mpr (Or.inr hu)
            have hu0 : u ≠ 0 := by
              have := ((OrderedSearch.mem_interiorIndices_iff J slot.a u).mp hu).1
              omega
            exact RouteExistence.nolink_linked J s slot u ⟨0, some (freeMultiples J s slot.a')⟩
              (freeMultiples J s slot.a') hus hB rfl hys hu0 (hf _ _ hult hz hu0)
          · apply from_A1
            have hdouble : ((2 * slot.a : ℕ) : ℤ) ≤ s := by
              exact le_trans (by exact_mod_cast hd.2.2.2.2.2) hsize
            have hxF : 2 * slot.a ∈ freeMultiples J s (Nat.lcm 2 slot.a) := by
              rw [(Arithmetic.odd_a_moduli slot hv hao).2.2.2]
              exact RouteExistence.free_self J s (2 * slot.a) hdouble hx
            intro hnil
            simpa only [hnil, List.not_mem_nil] using hxF

theorem DivisorGraphRuleH.H4 (J : List ℕ) (s : ℤ) (hJ : DivisorGraphRuleH.TablePathAt J s) (he : DivisorGraphRuleH.e J 1) :
    (∀ u w, u < J.length → w < J.length → u ≠ w → DivisorGraphRuleH.Feasible J u w) ∧
    (∀ slot : DivisorGraphRuleH.Slot, slot.Valid → (slot.size : ℤ) ≤ s →
      ∃ r, DivisorGraphRuleH.SearchReturns J s slot r) := by
  refine ⟨Feasibility.universal_feasibility J s hJ he, ?_⟩
  intro slot hv hsize
  exact RouteExistence.exists_route J s hJ he slot hv hsize
