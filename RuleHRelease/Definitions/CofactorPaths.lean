import Mathlib
import RuleHRelease.Definitions.OrderedSearch
set_option autoImplicit false
open DivisorGraphRuleH

theorem DivisorGraphRuleH.H3 (J : List ℕ) (s : ℤ) (hJ : TablePathAt J s)
    (slot : Slot) (hslot : slot.Valid) (hsize : (slot.size : ℤ) ≤ s)
    (r : Route) (hfound : SearchReturns J s slot r) :
    IsRoute J r ∧
    DivisorPath (cofactors J r) ∧
    (∀ c ∈ cofactors J r, (c : ℤ) ≤ s) ∧
    (∀ c, c ∈ cofactors J r ↔ c ∈ J ∨ r.x = some c ∨ r.y = some c) ∧
    (∀ x, r.x = some x → x ∉ J) ∧
    (∀ y, r.y = some y → y ∉ J) ∧
    (∀ x y, r.x = some x → r.y = some y → x ≠ y) ∧
    (∃ first last, (cofactors J r).head? = some first ∧
      (cofactors J r).getLast? = some last ∧ slot.a ∣ first ∧ slot.a' ∣ last) ∧
    (∀ x, r.x = some x →
      (r.u = lastIndex J → Even x ∧ 4 ≤ x) ∧
      (r.u = 0 → slot.a ∣ x ∧ 2 ≤ slot.a)) ∧
    (∀ y, r.y = some y →
      (r.w = lastIndex J → Even y ∧ 4 ≤ y) ∧
      (r.w = 0 → slot.a' ∣ y ∧ 2 ≤ slot.a')) := by
  obtain ⟨hr, hx, hy, hxy⟩ := OrderedSearch.search_sound J s hJ.1 slot hslot r hfound
  obtain ⟨_, _, _, _, hp, hh, ht, hperm⟩ :=
    H1 J s hJ r.u r.w hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
  have hmem (c : ℕ) : c ∈ (routeOrder J r.u r.w) ↔ c ∈ J := hperm.mem_iff
  have hset (c : ℕ) :
      c ∈ cofactors J r ↔ c ∈ J ∨ r.x = some c ∨ r.y = some c := by
    simp only [cofactors, List.mem_append, Option.mem_toList]
    rw [hmem c]
    tauto
  have hpositive : ∀ c ∈ cofactors J r, 0 < c := by
    intro c hc
    rcases (hset c).mp hc with hc | hc | hc
    · exact hJ.1.1.1 c hc
    · exact (hx.1 c hc).1
    · exact (hy.1 c hc).1
  have hbounded : ∀ c ∈ cofactors J r, (c : ℤ) ≤ s := by
    intro c hc
    rcases (hset c).mp hc with hc | hc | hc
    · exact hJ.2 c hc
    · exact (hx.1 c hc).2.1
    · exact (hy.1 c hc).2.1
  have hpre : DivisorPath (r.x.toList ++ (routeOrder J r.u r.w)) := by
    cases hxr : r.x with
    | none => simpa only [hxr, Option.toList_none, List.nil_append] using hp
    | some x =>
      obtain ⟨hxp, _, hxo, _, hxd, _, _⟩ := hx.1 x hxr
      have hxn : x ∉ (routeOrder J r.u r.w) := fun hm => hxo ((hmem x).mp hm)
      change DivisorPath ([x] ++ (routeOrder J r.u r.w))
      change (∀ c ∈ x :: (routeOrder J r.u r.w), 0 < c) ∧ (x :: (routeOrder J r.u r.w)).Nodup ∧ (x :: (routeOrder J r.u r.w)).IsChain Comparable
      refine ⟨?_, List.nodup_cons.mpr ⟨hxn, hp.2.1⟩, ?_⟩
      · intro c hc
        rcases List.mem_cons.mp hc with hcx | hcl
        · simpa only [hcx] using hxp
        · exact hp.1 c hcl
      · apply hp.2.2.cons
        intro t htm
        have he : term J r.u = t := by simpa only [hh, Option.mem_some_iff] using htm
        subst t
        exact Or.inr hxd
  have hpreLast : (r.x.toList ++ (routeOrder J r.u r.w)).getLast? = some (term J r.w) := by
    simp only [List.getLast?_append, ht, Option.some_or]
  have hfull : DivisorPath (cofactors J r) := by
    refine ⟨hpositive, ?_, ?_⟩
    · cases hyr : r.y with
      | none =>
        simpa only [cofactors, hyr, Option.toList_none, List.append_nil] using hpre.2.1
      | some y =>
        have hyn : y ∉ r.x.toList ++ (routeOrder J r.u r.w) := by
          intro hym
          rcases List.mem_append.mp hym with hym | hym
          · exact hxy y y (Option.mem_toList.mp hym) hyr rfl
          · exact (hy.1 y hyr).2.2.1 ((hmem y).mp hym)
        simp only [cofactors, hyr, Option.toList_some]
        change (r.x.toList ++ (routeOrder J r.u r.w) ++ [y]).Nodup
        apply List.nodup_append.mpr
        refine ⟨hpre.2.1, by simp, ?_⟩
        intro c hcm b hbm hcb
        have he : b = y := by simpa only [List.mem_singleton] using hbm
        subst b
        subst c
        exact hyn hcm
    · cases hyr : r.y with
      | none =>
        simpa only [cofactors, hyr, Option.toList_none, List.append_nil] using hpre.2.2
      | some y =>
        simp only [cofactors, hyr, Option.toList_some]
        change (r.x.toList ++ (routeOrder J r.u r.w) ++ [y]).IsChain Comparable
        apply hpre.2.2.append (by simp)
        intro t htm z hzm
        have hte : term J r.w = t := by
          simpa only [hpreLast, Option.mem_some_iff] using htm
        have hze : y = z := by simpa only [List.head?_cons, Option.mem_some_iff] using hzm
        subst t
        subst z
        exact Or.inl (hy.1 y hyr).2.2.2.2.1
  have hfirst : ∃ first, (cofactors J r).head? = some first ∧ slot.a ∣ first := by
    cases hxr : r.x with
    | none =>
      refine ⟨term J r.u, ?_, hx.2 hxr⟩
      simp only [cofactors, hxr, Option.toList_none, List.nil_append,
        List.head?_append, hh, Option.some_or]
    | some x =>
      refine ⟨x, ?_, (hx.1 x hxr).2.2.2.1⟩
      simp only [cofactors, hxr, Option.toList_some, List.cons_append,
        List.head?_cons]
  have hlast : ∃ last, (cofactors J r).getLast? = some last ∧ slot.a' ∣ last := by
    cases hyr : r.y with
    | none =>
      refine ⟨term J r.w, ?_, hy.2 hyr⟩
      simpa only [cofactors, hyr, Option.toList_none, List.append_nil] using hpreLast
    | some y =>
      refine ⟨y, ?_, (hy.1 y hyr).2.2.2.1⟩
      simp only [cofactors, hyr, Option.toList_some, List.getLast?_append,
        List.getLast?_singleton, Option.some_or]
  refine ⟨hr, hfull, hbounded, hset, ?_, ?_, hxy, ?_, ?_, ?_⟩
  · intro x hxr
    exact (hx.1 x hxr).2.2.1
  · intro y hyr
    exact (hy.1 y hyr).2.2.1
  · obtain ⟨first, hfirst, hdFirst⟩ := hfirst
    obtain ⟨last, hlast, hdLast⟩ := hlast
    exact ⟨first, last, hfirst, hlast, hdFirst, hdLast⟩
  · intro x hxr
    obtain ⟨_, _, _, hdx, _, htwo, hone⟩ := hx.1 x hxr
    exact ⟨htwo, fun hzero => ⟨hdx, hone hzero⟩⟩
  · intro y hyr
    obtain ⟨_, _, _, hdy, _, htwo, hone⟩ := hy.1 y hyr
    exact ⟨htwo, fun hzero => ⟨hdy, hone hzero⟩⟩

def DivisorGraphRuleH.CofactorPaths.results : Prop := True
