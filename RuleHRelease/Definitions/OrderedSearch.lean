import Mathlib
import RuleHRelease.Definitions.RouteValidity
open DivisorGraphRuleH DivisorGraphRuleH.OrderedSearch

set_option autoImplicit false

theorem DivisorGraphRuleH.OrderedSearch.mem_freeMultiples_iff (J : List ℕ) (s : ℤ) (m x : ℕ) :
    x ∈ DivisorGraphRuleH.freeMultiples J s m ↔
      m ≤ x ∧ m ∣ x ∧ (x : ℤ) ≤ s ∧ x ∉ J := by
  simp only [freeMultiples, List.mem_filter, Foundation.mem_up, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hm, _⟩, hd, hs, hn⟩
    exact ⟨hm, hd, hs, hn⟩
  · rintro ⟨hm, hd, hs, hn⟩
    exact ⟨⟨hm, by omega⟩, hd, hs, hn⟩

theorem DivisorGraphRuleH.OrderedSearch.mem_interiorIndices_iff (J : List ℕ) (m i : ℕ) :
    i ∈ DivisorGraphRuleH.interiorIndices J m ↔
      1 ≤ i ∧ i < DivisorGraphRuleH.lastIndex J ∧ m ∣ DivisorGraphRuleH.term J i := by
  simp only [interiorIndices, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by unfold lastIndex at h; omega, h⟩

theorem DivisorGraphRuleH.OrderedSearch.feasible_ne (J : List ℕ) (u w : ℕ) (h : DivisorGraphRuleH.Feasible J u w) : u ≠ w := by
  intro heq
  subst w
  simpa [Feasible, H] using h

theorem DivisorGraphRuleH.OrderedSearch.feasible_endpoints (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) (u w : ℕ)
    (hu : u = 0 ∨ u = DivisorGraphRuleH.lastIndex J)
    (hw : w = 0 ∨ w = DivisorGraphRuleH.lastIndex J) (hne : u ≠ w) :
    DivisorGraphRuleH.Feasible J u w := by
  have hn := Foundation.lastIndex_bounds J hJ
  have hf : forwardH J 0 (lastIndex J) = some (up 0 (lastIndex J)) := by
    simp [forwardH, hn.1, hn.2.2.1, Nat.ne_of_gt hn.1]
  rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
  · exact (hne rfl).elim
  · simp [Feasible, H, Nat.zero_lt_of_lt hn.1, hf]
  · simp [Feasible, H, Nat.zero_lt_of_lt hn.1, hf]
  · exact (hne rfl).elim

theorem DivisorGraphRuleH.OrderedSearch.link_zero (J : List ℕ) (s : ℤ) (hJ : DivisorGraphRuleH.TablePath J)
    (m x : ℕ) (hm : 2 ≤ m) (hx : x ∈ DivisorGraphRuleH.freeMultiples J s m) :
    DivisorGraphRuleH.OrderedSearch.LinkValid J s m 0 x := by
  obtain ⟨hlo, hd, hs, hout⟩ := (mem_freeMultiples_iff J s m x).mp hx
  have hn := (Foundation.lastIndex_bounds J hJ).1
  refine ⟨by omega, hs, hout, hd, ?_, ?_, fun _ => hm⟩
  · rw [Foundation.term_first J hJ]
    exact one_dvd x
  · intro hz
    omega

theorem DivisorGraphRuleH.OrderedSearch.link_last (J : List ℕ) (s : ℤ) (hJ : DivisorGraphRuleH.TablePath J)
    (m x : ℕ) (hm : 0 < m)
    (hx : x ∈ DivisorGraphRuleH.freeMultiples J s (Nat.lcm 2 m)) :
    DivisorGraphRuleH.OrderedSearch.LinkValid J s m (DivisorGraphRuleH.lastIndex J) x := by
  obtain ⟨hlo, hd, hs, hout⟩ := (mem_freeMultiples_iff J s (Nat.lcm 2 m) x).mp hx
  have hmdiv : m ∣ x := dvd_trans (Nat.dvd_lcm_right 2 m) hd
  have htwo : 2 ∣ x := dvd_trans (Nat.dvd_lcm_left 2 m) hd
  have hlpos : 0 < Nat.lcm 2 m := Nat.lcm_pos (by decide) hm
  have hpos : 0 < x := lt_of_lt_of_le hlpos hlo
  have hx2 : x ≠ 2 := fun h => hout (h ▸ (Foundation.tablePath_endpoints_mem J hJ).2)
  obtain ⟨k, hk⟩ := htwo
  have he : Even x := ⟨k, by omega⟩
  have hn := (Foundation.lastIndex_bounds J hJ).1
  refine ⟨hpos, hs, hout, hmdiv, ?_, fun _ => ⟨he, by omega⟩, ?_⟩
  · rw [Foundation.term_last J hJ]
    exact ⟨k, hk⟩
  · intro hz
    omega

theorem DivisorGraphRuleH.OrderedSearch.options_valid (J : List ℕ) (s : ℤ) (hJ : DivisorGraphRuleH.TablePath J)
    (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) :
    (∀ A ∈ DivisorGraphRuleH.startOptions J s slot,
      DivisorGraphRuleH.OrderedSearch.OptionValid J s slot.a A) ∧
    (∀ B ∈ DivisorGraphRuleH.endOptions J s slot,
      DivisorGraphRuleH.OrderedSearch.OptionValid J s slot.a' B) := by
  have hn := Foundation.lastIndex_bounds J hJ
  have hz : 0 < J.length := by omega
  have hnvalid : lastIndex J < J.length := hn.2.2.1
  constructor
  · intro A hA
    simp only [startOptions, List.mem_filterMap, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hA
    obtain ⟨o, ho, heq⟩ := hA
    change o = some A at heq
    rcases ho with rfl | rfl | rfl
    · dsimp only [A1] at heq
      split at heq
      · cases heq
      · cases heq
        refine ⟨Or.inr rfl, hnvalid, ?_⟩
        exact ⟨by assumption, fun x hx => link_last J s hJ slot.a x (Arithmetic.a_pos slot hv) hx⟩
    · dsimp only [A2] at heq
      split at heq
      · cases heq
        exact ⟨Or.inr rfl, hnvalid, by rw [Foundation.term_last J hJ]; assumption⟩
      · cases heq
    · dsimp only [A3] at heq
      split at heq
      · cases heq
        refine ⟨Or.inl rfl, hz, ?_⟩
        change slot.a ∣ term J 0
        rw [Foundation.term_first J hJ, show slot.a = 1 by assumption]
      · split at heq
        · split at heq
          · cases heq
          · cases heq
            exact ⟨Or.inl rfl, hz, by assumption,
              fun x hx => link_zero J s hJ slot.a x (by assumption) hx⟩
        · cases heq
  · intro A hA
    simp only [endOptions, List.mem_filterMap, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hA
    obtain ⟨o, ho, heq⟩ := hA
    change o = some A at heq
    rcases ho with rfl | rfl | rfl
    · dsimp only [B1] at heq
      split at heq
      · cases heq
      · cases heq
        exact ⟨Or.inl rfl, hz, by assumption,
          fun x hx => link_zero J s hJ slot.a' x (Arithmetic.two_le_aprime slot hv) hx⟩
    · dsimp only [B2] at heq
      split at heq
      · cases heq
      · cases heq
        exact ⟨Or.inr rfl, hnvalid, by assumption,
          fun x hx => link_last J s hJ slot.a' x (Arithmetic.aprime_pos slot hv) hx⟩
    · dsimp only [B3] at heq
      split at heq
      · cases heq
        exact ⟨Or.inr rfl, hnvalid, by rw [Foundation.term_last J hJ]; assumption⟩
      · cases heq

theorem DivisorGraphRuleH.OrderedSearch.mem_R1_iff (J : List ℕ) (s : ℤ) (slot : DivisorGraphRuleH.Slot) (r : DivisorGraphRuleH.Route) :
    r ∈ DivisorGraphRuleH.R1 J s slot ↔
      ∃ A ∈ DivisorGraphRuleH.startOptions J s slot,
      ∃ B ∈ DivisorGraphRuleH.endOptions J s slot,
        A.index ≠ B.index ∧ ∃ xs ys x y,
          A.links = some xs ∧ B.links = some ys ∧ xs.head? = some x ∧
          ys.find? (fun y => decide (y ≠ x)) = some y ∧
          r = ⟨some x, A.index, B.index, some y⟩ := by
  simp only [R1, List.mem_flatMap]
  apply exists_congr
  intro A
  apply and_congr_right
  intro hA
  apply exists_congr
  intro B
  apply and_congr_right
  intro hB
  by_cases hi : A.index = B.index
  · simp [hi]
  · simp only [if_neg hi]
    cases hx : A.links with
    | none => simp [hx]
    | some xs =>
      cases hy : B.links with
      | none => simp [hy]
      | some ys =>
        constructor
        · intro hr
          have hr' := Option.mem_toList.mp hr
          obtain ⟨x, hhead, hrest⟩ := Option.bind_eq_some_iff.mp hr'
          obtain ⟨y, hfind, heq⟩ := Option.map_eq_some_iff.mp hrest
          exact ⟨hi, xs, ys, x, y, rfl, rfl, hhead, hfind, heq.symm⟩
        · rintro ⟨_, xs', ys', x, y, hxs, hys, hhead, hfind, rfl⟩
          cases hxs
          cases hys
          apply Option.mem_toList.mpr
          exact Option.bind_eq_some_iff.mpr
            ⟨x, hhead, Option.map_eq_some_iff.mpr ⟨y, hfind, rfl⟩⟩

theorem DivisorGraphRuleH.OrderedSearch.mem_R2_iff (J : List ℕ) (s : ℤ) (slot : DivisorGraphRuleH.Slot) (r : DivisorGraphRuleH.Route) :
    r ∈ DivisorGraphRuleH.R2 J s slot ↔
      ∃ A ∈ DivisorGraphRuleH.startOptions J s slot,
      ∃ B ∈ DivisorGraphRuleH.endOptions J s slot,
        A.index ≠ B.index ∧
        ((∃ xs x, A.links = some xs ∧ B.links = none ∧ xs.head? = some x ∧
          r = ⟨some x, A.index, B.index, none⟩) ∨
         (∃ ys y, A.links = none ∧ B.links = some ys ∧ ys.head? = some y ∧
          r = ⟨none, A.index, B.index, some y⟩)) := by
  simp only [R2, List.mem_flatMap]
  apply exists_congr
  intro A
  apply and_congr_right
  intro hA
  apply exists_congr
  intro B
  apply and_congr_right
  intro hB
  by_cases hi : A.index = B.index
  · simp [hi]
  · simp only [if_neg hi]
    cases hx : A.links <;> cases hy : B.links <;>
      simp [hx, hy, hi, Option.bind_eq_some_iff, Option.map_eq_some_iff, eq_comm]

theorem DivisorGraphRuleH.OrderedSearch.mem_R3_iff (J : List ℕ) (s : ℤ) (slot : DivisorGraphRuleH.Slot) (r : DivisorGraphRuleH.Route) :
    r ∈ DivisorGraphRuleH.R3 J s slot ↔
      ∃ A ∈ DivisorGraphRuleH.startOptions J s slot, ∃ xs w x,
        A.links = some xs ∧ w ∈ DivisorGraphRuleH.interiorIndices J slot.a' ∧
        DivisorGraphRuleH.Feasible J A.index w ∧ xs.head? = some x ∧
        r = ⟨some x, A.index, w, none⟩ := by
  simp only [R3, List.mem_flatMap]
  apply exists_congr
  intro A
  apply and_congr_right
  intro hA
  cases hx : A.links with
  | none => simp [hx]
  | some xs =>
    simp only [hx, List.mem_flatMap]
    constructor
    · rintro ⟨w, hw, hr⟩
      split at hr
      · simp only [Option.mem_toList, Option.map_eq_some_iff] at hr
        obtain ⟨x, hhead, heq⟩ := hr
        exact ⟨xs, w, x, rfl, hw, by assumption, hhead, heq.symm⟩
      · simp at hr
    · rintro ⟨ys, w, x, hys, hw, hf, hhead, rfl⟩
      cases hys
      exact ⟨w, hw, by simp [hf, hhead]⟩

theorem DivisorGraphRuleH.OrderedSearch.mem_R4_iff (J : List ℕ) (s : ℤ) (slot : DivisorGraphRuleH.Slot) (r : DivisorGraphRuleH.Route) :
    r ∈ DivisorGraphRuleH.R4 J s slot ↔
      ∃ u ∈ DivisorGraphRuleH.interiorIndices J slot.a,
      ∃ B ∈ DivisorGraphRuleH.endOptions J s slot, ∃ ys y,
        B.links = some ys ∧ DivisorGraphRuleH.Feasible J u B.index ∧
        ys.head? = some y ∧ r = ⟨none, u, B.index, some y⟩ := by
  simp only [R4, List.mem_flatMap]
  apply exists_congr
  intro u
  apply and_congr_right
  intro hu
  apply exists_congr
  intro B
  apply and_congr_right
  intro hB
  cases hy : B.links with
  | none => simp [hy]
  | some ys =>
    simp only [hy]
    by_cases hf : Feasible J u B.index
    · simp [hf, Option.map_eq_some_iff, eq_comm]
    · simp [hf]

theorem DivisorGraphRuleH.OrderedSearch.mem_R5_iff (J : List ℕ) (s : ℤ) (slot : DivisorGraphRuleH.Slot) (r : DivisorGraphRuleH.Route) :
    r ∈ DivisorGraphRuleH.R5 J s slot ↔
      ∃ u ∈ DivisorGraphRuleH.noLinkStarts J s slot,
      ∃ w ∈ DivisorGraphRuleH.noLinkEnds J s slot,
        u ≠ w ∧ DivisorGraphRuleH.Feasible J u w ∧ r = ⟨none, u, w, none⟩ := by
  simp only [R5, List.mem_flatMap]
  apply exists_congr
  intro u
  apply and_congr_right
  intro hu
  apply exists_congr
  intro w
  apply and_congr_right
  intro hw
  by_cases hf : u ≠ w ∧ Feasible J u w
  · simp [hf.1, hf.2]
  · simp only [if_neg hf, List.not_mem_nil, false_iff]
    rintro ⟨hne, hfeas, _⟩
    exact hf ⟨hne, hfeas⟩

theorem DivisorGraphRuleH.OrderedSearch.noLink_valid (J : List ℕ) (s : ℤ) (hJ : DivisorGraphRuleH.TablePath J)
    (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) :
    (∀ u ∈ DivisorGraphRuleH.noLinkStarts J s slot,
      u < J.length ∧ slot.a ∣ DivisorGraphRuleH.term J u) ∧
    (∀ w ∈ DivisorGraphRuleH.noLinkEnds J s slot,
      w < J.length ∧ slot.a' ∣ DivisorGraphRuleH.term J w) := by
  have aux (m : ℕ) (opts : List EndpointOption)
      (hopts : ∀ A ∈ opts, OptionValid J s m A) :
      ∀ i ∈ opts.filterMap (fun A => if A.links.isNone then some A.index else none) ++
        interiorIndices J m, i < J.length ∧ m ∣ term J i := by
    intro i hi
    simp only [List.mem_append, List.mem_filterMap] at hi
    rcases hi with ⟨A, hA, hr⟩ | hi
    · have hvalid := hopts A hA
      cases hl : A.links with
      | none =>
        simp only [hl, Option.isNone_none, ite_true, Option.some.injEq] at hr
        subst i
        exact ⟨hvalid.2.1, by simpa only [hl] using hvalid.2.2⟩
      | some xs => simp [hl] at hr
    · have ht := (mem_interiorIndices_iff J m i).mp hi
      exact ⟨lt_trans ht.2.1 (Foundation.lastIndex_bounds J hJ).2.2.1, ht.2.2⟩
  exact ⟨aux slot.a (startOptions J s slot) (options_valid J s hJ slot hv).1,
    aux slot.a' (endOptions J s slot) (options_valid J s hJ slot hv).2⟩

theorem DivisorGraphRuleH.OrderedSearch.R1_sound (J : List ℕ) (s : ℤ) (hJ : DivisorGraphRuleH.TablePath J)
    (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) (r : DivisorGraphRuleH.Route)
    (hr : r ∈ DivisorGraphRuleH.R1 J s slot) :
    DivisorGraphRuleH.OrderedSearch.CandidateValid J s slot r := by
  obtain ⟨A, hA, B, hB, hne, xs, ys, x, y, hxs, hys, hhead, hfind, rfl⟩ :=
    (mem_R1_iff J s slot r).mp hr
  have va := (options_valid J s hJ slot hv).1 A hA
  have vb := (options_valid J s hJ slot hv).2 B hB
  have vx : LinkValid J s slot.a A.index x := by
    have h := va.2.2
    rw [hxs] at h
    exact h.2 x (List.mem_of_head? hhead)
  have vy : LinkValid J s slot.a' B.index y := by
    have h := vb.2.2
    rw [hys] at h
    exact h.2 y (List.mem_of_find?_eq_some hfind)
  have hyx : y ≠ x := of_decide_eq_true (List.find?_some (p := fun z : ℕ => decide (z ≠ x)) hfind)
  refine ⟨⟨va.2.1, vb.2.1, hne,
    feasible_endpoints J hJ A.index B.index va.1 vb.1 hne⟩, ?_, ?_, ?_⟩
  · exact ⟨fun z hz => (by cases hz; exact vx), fun h => (by cases h)⟩
  · exact ⟨fun z hz => (by cases hz; exact vy), fun h => (by cases h)⟩
  · intro a b ha hb
    cases ha
    cases hb
    exact hyx.symm

theorem DivisorGraphRuleH.OrderedSearch.R2_sound (J : List ℕ) (s : ℤ) (hJ : DivisorGraphRuleH.TablePath J)
    (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) (r : DivisorGraphRuleH.Route)
    (hr : r ∈ DivisorGraphRuleH.R2 J s slot) :
    DivisorGraphRuleH.OrderedSearch.CandidateValid J s slot r := by
  obtain ⟨A, hA, B, hB, hne, hcase⟩ := (mem_R2_iff J s slot r).mp hr
  have va := (options_valid J s hJ slot hv).1 A hA
  have vb := (options_valid J s hJ slot hv).2 B hB
  have hf := feasible_endpoints J hJ A.index B.index va.1 vb.1 hne
  rcases hcase with ⟨xs, x, hxs, hbn, hhead, rfl⟩ | ⟨ys, y, han, hys, hhead, rfl⟩
  · have vx : LinkValid J s slot.a A.index x := by
      have h := va.2.2
      rw [hxs] at h
      exact h.2 x (List.mem_of_head? hhead)
    have vn : slot.a' ∣ term J B.index := by simpa only [hbn] using vb.2.2
    refine ⟨⟨va.2.1, vb.2.1, hne, hf⟩, ?_, ?_, ?_⟩
    · exact ⟨fun z hz => (by cases hz; exact vx), fun h => (by cases h)⟩
    · exact ⟨fun z hz => (by cases hz), fun _ => vn⟩
    · intro a b _ hb
      cases hb
  · have vy : LinkValid J s slot.a' B.index y := by
      have h := vb.2.2
      rw [hys] at h
      exact h.2 y (List.mem_of_head? hhead)
    have vn : slot.a ∣ term J A.index := by simpa only [han] using va.2.2
    refine ⟨⟨va.2.1, vb.2.1, hne, hf⟩, ?_, ?_, ?_⟩
    · exact ⟨fun z hz => (by cases hz), fun _ => vn⟩
    · exact ⟨fun z hz => (by cases hz; exact vy), fun h => (by cases h)⟩
    · intro a b ha _
      cases ha

theorem DivisorGraphRuleH.OrderedSearch.R3_sound (J : List ℕ) (s : ℤ) (hJ : DivisorGraphRuleH.TablePath J)
    (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) (r : DivisorGraphRuleH.Route)
    (hr : r ∈ DivisorGraphRuleH.R3 J s slot) :
    DivisorGraphRuleH.OrderedSearch.CandidateValid J s slot r := by
  obtain ⟨A, hA, xs, w, x, hxs, hw, hf, hhead, rfl⟩ := (mem_R3_iff J s slot r).mp hr
  have va := (options_valid J s hJ slot hv).1 A hA
  have vw := (mem_interiorIndices_iff J slot.a' w).mp hw
  have vx : LinkValid J s slot.a A.index x := by
    have h := va.2.2
    rw [hxs] at h
    exact h.2 x (List.mem_of_head? hhead)
  refine ⟨⟨va.2.1, lt_trans vw.2.1 (Foundation.lastIndex_bounds J hJ).2.2.1,
    feasible_ne J A.index w hf, hf⟩, ?_, ?_, ?_⟩
  · exact ⟨fun z hz => (by cases hz; exact vx), fun h => (by cases h)⟩
  · exact ⟨fun z hz => (by cases hz), fun _ => vw.2.2⟩
  · intro a b _ hb
    cases hb

theorem DivisorGraphRuleH.OrderedSearch.R4_sound (J : List ℕ) (s : ℤ) (hJ : DivisorGraphRuleH.TablePath J)
    (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) (r : DivisorGraphRuleH.Route)
    (hr : r ∈ DivisorGraphRuleH.R4 J s slot) :
    DivisorGraphRuleH.OrderedSearch.CandidateValid J s slot r := by
  obtain ⟨u, hu, B, hB, ys, y, hys, hf, hhead, rfl⟩ := (mem_R4_iff J s slot r).mp hr
  have vu := (mem_interiorIndices_iff J slot.a u).mp hu
  have vb := (options_valid J s hJ slot hv).2 B hB
  have vy : LinkValid J s slot.a' B.index y := by
    have h := vb.2.2
    rw [hys] at h
    exact h.2 y (List.mem_of_head? hhead)
  refine ⟨⟨lt_trans vu.2.1 (Foundation.lastIndex_bounds J hJ).2.2.1, vb.2.1,
    feasible_ne J u B.index hf, hf⟩, ?_, ?_, ?_⟩
  · exact ⟨fun z hz => (by cases hz), fun _ => vu.2.2⟩
  · exact ⟨fun z hz => (by cases hz; exact vy), fun h => (by cases h)⟩
  · intro a b ha _
    cases ha

theorem DivisorGraphRuleH.OrderedSearch.R5_sound (J : List ℕ) (s : ℤ) (hJ : DivisorGraphRuleH.TablePath J)
    (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) (r : DivisorGraphRuleH.Route)
    (hr : r ∈ DivisorGraphRuleH.R5 J s slot) :
    DivisorGraphRuleH.OrderedSearch.CandidateValid J s slot r := by
  obtain ⟨u, hu, w, hw, hne, hf, rfl⟩ := (mem_R5_iff J s slot r).mp hr
  have vu := (noLink_valid J s hJ slot hv).1 u hu
  have vw := (noLink_valid J s hJ slot hv).2 w hw
  exact ⟨⟨vu.1, vw.1, hne, hf⟩,
    ⟨fun z hz => (by cases hz), fun _ => vu.2⟩,
    ⟨fun z hz => (by cases hz), fun _ => vw.2⟩,
    fun a b ha _ => (by cases ha)⟩

theorem DivisorGraphRuleH.OrderedSearch.routesOfKind_sound (J : List ℕ) (s : ℤ) (hJ : DivisorGraphRuleH.TablePath J)
    (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) (kind : DivisorGraphRuleH.RouteKind)
    (r : DivisorGraphRuleH.Route) (hr : r ∈ DivisorGraphRuleH.routesOfKind J s slot kind) :
    DivisorGraphRuleH.OrderedSearch.CandidateValid J s slot r := by
  cases kind with
  | R1 => exact R1_sound J s hJ slot hv r hr
  | R2 => exact R2_sound J s hJ slot hv r hr
  | R3 => exact R3_sound J s hJ slot hv r hr
  | R4 => exact R4_sound J s hJ slot hv r hr
  | R5 => exact R5_sound J s hJ slot hv r hr

theorem DivisorGraphRuleH.OrderedSearch.search_first_iff (J : List ℕ) (s : ℤ) (slot : DivisorGraphRuleH.Slot) (r : DivisorGraphRuleH.Route) :
    DivisorGraphRuleH.SearchReturns J s slot r ↔
      ∃ kind tail, DivisorGraphRuleH.rankedRoutes J s slot = (kind, r) :: tail := by
  cases hl : rankedRoutes J s slot with
  | nil => simp [SearchReturns, selectedRoute, hl]
  | cons kr tail =>
    rcases kr with ⟨kind, q⟩
    simp [SearchReturns, selectedRoute, hl]

theorem DivisorGraphRuleH.OrderedSearch.search_exists_iff (J : List ℕ) (s : ℤ) (slot : DivisorGraphRuleH.Slot) :
    (∃ r, DivisorGraphRuleH.SearchReturns J s slot r) ↔
      DivisorGraphRuleH.rankedRoutes J s slot ≠ [] := by
  constructor
  · rintro ⟨r, hr⟩ hnil
    simp [SearchReturns, selectedRoute, hnil] at hr
  · intro hn
    cases hl : rankedRoutes J s slot with
    | nil => exact (hn hl).elim
    | cons kr tail =>
      exact ⟨kr.2, by simp [SearchReturns, selectedRoute, hl]⟩

theorem DivisorGraphRuleH.OrderedSearch.search_of_mem_kind (J : List ℕ) (s : ℤ) (slot : DivisorGraphRuleH.Slot)
    (kind : DivisorGraphRuleH.RouteKind) (r : DivisorGraphRuleH.Route)
    (hr : r ∈ DivisorGraphRuleH.routesOfKind J s slot kind) :
    ∃ selected, DivisorGraphRuleH.SearchReturns J s slot selected := by
  apply (search_exists_iff J s slot).mpr
  have hk : kind ∈ [RouteKind.R1, .R2, .R3, .R4, .R5] := by
    cases kind <;> simp
  have hm : (kind, r) ∈ rankedRoutes J s slot :=
    List.mem_flatMap.mpr ⟨kind, hk, List.mem_map.mpr ⟨r, hr, rfl⟩⟩
  intro hn
  simpa only [hn, List.not_mem_nil] using hm

theorem DivisorGraphRuleH.OrderedSearch.search_sound (J : List ℕ) (s : ℤ) (hJ : DivisorGraphRuleH.TablePath J)
    (slot : DivisorGraphRuleH.Slot) (hv : slot.Valid) (r : DivisorGraphRuleH.Route)
    (hr : DivisorGraphRuleH.SearchReturns J s slot r) :
    DivisorGraphRuleH.OrderedSearch.CandidateValid J s slot r := by
  obtain ⟨kind, tail, hfirst⟩ := (search_first_iff J s slot r).mp hr
  have hm : (kind, r) ∈ rankedRoutes J s slot := by
    rw [hfirst]
    exact List.mem_cons_self
  obtain ⟨k, _, hmap⟩ := List.mem_flatMap.mp hm
  obtain ⟨q', hq', heq'⟩ := List.mem_map.mp hmap
  have hk : k = kind := congrArg Prod.fst heq'
  have hqr : q' = r := congrArg Prod.snd heq'
  subst k
  subst q'
  exact routesOfKind_sound J s hJ slot hv kind r hq'

def DivisorGraphRuleH.OrderedSearch.results : Prop := True
