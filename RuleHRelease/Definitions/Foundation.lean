import Mathlib
import RuleHRelease.Definitions.Core
set_option autoImplicit false
open DivisorGraphRuleH

theorem DivisorGraphRuleH.Foundation.tablePath_parts (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) :
    (∀ x ∈ J, 0 < x) ∧ J.Nodup ∧ J.IsChain DivisorGraphRuleH.Comparable ∧
    J.head? = some 1 ∧ J.getLast? = some 2 := by
  exact ⟨hJ.1.1, hJ.1.2.1, hJ.1.2.2, hJ.2.1, hJ.2.2⟩

theorem DivisorGraphRuleH.Foundation.tablePath_length (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) : 2 ≤ J.length := by
  cases J with
  | nil =>
    have h := hJ.2.1
    simp only [List.head?_nil, reduceCtorEq] at h
  | cons a rest =>
    cases rest with
    | nil =>
      have hfirst := hJ.2.1
      have hlast := hJ.2.2
      simp only [List.head?_cons, Option.some.injEq] at hfirst
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      omega
    | cons b rest => simp

theorem DivisorGraphRuleH.Foundation.lastIndex_bounds (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) :
    1 ≤ DivisorGraphRuleH.lastIndex J ∧ DivisorGraphRuleH.lastIndex J + 1 = J.length ∧
    DivisorGraphRuleH.lastIndex J < J.length ∧ (∀ i : ℕ, i < J.length ↔ i ≤ DivisorGraphRuleH.lastIndex J) := by
  have hl := DivisorGraphRuleH.Foundation.tablePath_length J hJ
  unfold lastIndex
  refine ⟨?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · intro i
    omega

theorem DivisorGraphRuleH.Foundation.tablePath_endpoints_mem (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) : 1 ∈ J ∧ 2 ∈ J := by
  exact ⟨List.mem_of_head? hJ.2.1, List.mem_of_getLast? hJ.2.2⟩

theorem DivisorGraphRuleH.Foundation.term_getElem (J : List ℕ) (i : ℕ) (hi : i < J.length) : DivisorGraphRuleH.term J i = J[i] := by
  exact (List.getElem_eq_getD 0).symm

theorem DivisorGraphRuleH.Foundation.term_mem (J : List ℕ) (i : ℕ) (hi : i < J.length) : DivisorGraphRuleH.term J i ∈ J := by
  rw [DivisorGraphRuleH.Foundation.term_getElem J i hi]
  exact List.getElem_mem hi

theorem DivisorGraphRuleH.Foundation.term_index_of_mem (J : List ℕ) (x : ℕ) (hx : x ∈ J) :
    ∃ i : ℕ, i < J.length ∧ DivisorGraphRuleH.term J i = x := by
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hx
  exact ⟨i, hi, (DivisorGraphRuleH.Foundation.term_getElem J i hi).trans heq⟩

theorem DivisorGraphRuleH.Foundation.term_injective (J : List ℕ) (hJ : J.Nodup) (i j : ℕ)
    (hi : i < J.length) (hj : j < J.length) :
    DivisorGraphRuleH.term J i = DivisorGraphRuleH.term J j ↔ i = j := by
  exact List.getD_inj hi hj hJ

theorem DivisorGraphRuleH.Foundation.term_first (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) : DivisorGraphRuleH.term J 0 = 1 := by
  change (J[0]?).getD 0 = 1
  rw [← List.head?_eq_getElem?, hJ.2.1]
  rfl

theorem DivisorGraphRuleH.Foundation.term_last (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) : DivisorGraphRuleH.term J (DivisorGraphRuleH.lastIndex J) = 2 := by
  change (J[J.length - 1]?).getD 0 = 2
  rw [← List.getLast?_eq_getElem?, hJ.2.2]
  rfl

theorem DivisorGraphRuleH.Foundation.term_pos (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) (i : ℕ) (hi : i < J.length) :
    0 < DivisorGraphRuleH.term J i := by
  exact hJ.1.1 _ (DivisorGraphRuleH.Foundation.term_mem J i hi)

theorem DivisorGraphRuleH.Foundation.term_le_range (J : List ℕ) (s : ℤ) (hJ : DivisorGraphRuleH.TablePathAt J s)
    (i : ℕ) (hi : i < J.length) : (DivisorGraphRuleH.term J i : ℤ) ≤ s := by
  exact hJ.2 _ (DivisorGraphRuleH.Foundation.term_mem J i hi)

theorem DivisorGraphRuleH.Foundation.tablePathAt_two_le (J : List ℕ) (s : ℤ) (hJ : DivisorGraphRuleH.TablePathAt J s) : (2 : ℤ) ≤ s := by
  exact hJ.2 2 (DivisorGraphRuleH.Foundation.tablePath_endpoints_mem J hJ.1).2

theorem DivisorGraphRuleH.Foundation.term_adjacent (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J)
    (i : ℕ) (hi : i + 1 < J.length) :
    DivisorGraphRuleH.Comparable (DivisorGraphRuleH.term J i) (DivisorGraphRuleH.term J (i + 1)) := by
  have hi0 : i < J.length := by omega
  rw [DivisorGraphRuleH.Foundation.term_getElem J i hi0, DivisorGraphRuleH.Foundation.term_getElem J (i + 1) hi]
  exact hJ.1.2.2.getElem i hi

theorem DivisorGraphRuleH.Foundation.term_map_range (J : List ℕ) : (List.range J.length).map (DivisorGraphRuleH.term J) = J := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simpa only [List.getElem_map, List.getElem_range] using DivisorGraphRuleH.Foundation.term_getElem J i hj

theorem DivisorGraphRuleH.Foundation.up_length (lo hi : ℕ) : (DivisorGraphRuleH.up lo hi).length = hi + 1 - lo := by
  exact List.length_range'

theorem DivisorGraphRuleH.Foundation.mem_up (lo hi x : ℕ) : x ∈ DivisorGraphRuleH.up lo hi ↔ lo ≤ x ∧ x ≤ hi := by
  simp only [up, List.mem_range'_1]
  omega

theorem DivisorGraphRuleH.Foundation.up_nodup (lo hi : ℕ) : (DivisorGraphRuleH.up lo hi).Nodup := by
  exact List.nodup_range'

theorem DivisorGraphRuleH.Foundation.up_eq_nil (lo hi : ℕ) : DivisorGraphRuleH.up lo hi = [] ↔ hi < lo := by
  rw [← List.length_eq_zero_iff, DivisorGraphRuleH.Foundation.up_length]
  omega

theorem DivisorGraphRuleH.Foundation.up_endpoints (lo hi : ℕ) (h : lo ≤ hi) :
    (DivisorGraphRuleH.up lo hi).head? = some lo ∧ (DivisorGraphRuleH.up lo hi).getLast? = some hi := by
  have hz : hi + 1 - lo ≠ 0 := by omega
  simp only [up, List.head?_range', List.getLast?_range', hz, if_false]
  constructor
  · trivial
  · congr 1
    omega

theorem DivisorGraphRuleH.Foundation.up_getElem (lo hi i : ℕ) (h : i < (DivisorGraphRuleH.up lo hi).length) :
    (DivisorGraphRuleH.up lo hi)[i] = lo + i := by
  simpa only [up, List.getElem_range', Nat.one_mul]

theorem DivisorGraphRuleH.Foundation.down_length (hi lo : ℕ) : (DivisorGraphRuleH.down hi lo).length = hi + 1 - lo := by
  simp only [down, List.length_reverse, DivisorGraphRuleH.Foundation.up_length]

theorem DivisorGraphRuleH.Foundation.mem_down (hi lo x : ℕ) : x ∈ DivisorGraphRuleH.down hi lo ↔ lo ≤ x ∧ x ≤ hi := by
  simp only [down, List.mem_reverse, DivisorGraphRuleH.Foundation.mem_up]

theorem DivisorGraphRuleH.Foundation.down_nodup (hi lo : ℕ) : (DivisorGraphRuleH.down hi lo).Nodup := by
  exact List.nodup_reverse.mpr (DivisorGraphRuleH.Foundation.up_nodup lo hi)

theorem DivisorGraphRuleH.Foundation.down_eq_nil (hi lo : ℕ) : DivisorGraphRuleH.down hi lo = [] ↔ hi < lo := by
  simp [down, DivisorGraphRuleH.Foundation.up_eq_nil]

theorem DivisorGraphRuleH.Foundation.down_endpoints (hi lo : ℕ) (h : lo ≤ hi) :
    (DivisorGraphRuleH.down hi lo).head? = some hi ∧ (DivisorGraphRuleH.down hi lo).getLast? = some lo := by
  have hu := DivisorGraphRuleH.Foundation.up_endpoints lo hi h
  simpa only [down, List.head?_reverse, List.getLast?_reverse] using And.intro hu.2 hu.1

theorem DivisorGraphRuleH.Foundation.down_getElem (hi lo i : ℕ) (h : i < (DivisorGraphRuleH.down hi lo).length) :
    (DivisorGraphRuleH.down hi lo)[i] = hi - i := by
  have hb : i < hi + 1 - lo := by simpa only [down, List.length_reverse, DivisorGraphRuleH.Foundation.up_length] using h
  simp only [down, List.getElem_reverse, up, List.getElem_range', List.length_range', Nat.one_mul]
  omega


def DivisorGraphRuleH.Foundation.results : Unit := ()
