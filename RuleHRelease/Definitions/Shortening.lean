import Mathlib
import RuleHRelease.Definitions.Foundation
set_option autoImplicit false
open DivisorGraphRuleH

theorem DivisorGraphRuleH.R0 (J : List ℕ) (hJ : TablePath J) (hn : 2 ≤ lastIndex J) :
    e J (lastIndex J - 1) ∧ 4 ≤ term J (lastIndex J - 1) := by
  have hb := Foundation.lastIndex_bounds J hJ
  have hi : lastIndex J - 1 < J.length := by omega
  have hi0 : 0 < J.length := by omega
  have hne1 : term J (lastIndex J - 1) ≠ 1 := by
    intro h
    have heq : lastIndex J - 1 = 0 :=
      (Foundation.term_injective J hJ.1.2.1 _ _ hi hi0).mp (h.trans (Foundation.term_first J hJ).symm)
    omega
  have hne2 : term J (lastIndex J - 1) ≠ 2 := by
    intro h
    have heq : lastIndex J - 1 = lastIndex J :=
      (Foundation.term_injective J hJ.1.2.1 _ _ hi hb.2.2.1).mp (h.trans (Foundation.term_last J hJ).symm)
    omega
  have hadj := Foundation.term_adjacent J hJ (lastIndex J - 1) (by omega)
  have hsucc : lastIndex J - 1 + 1 = lastIndex J := by omega
  rw [hsucc, Foundation.term_last J hJ] at hadj
  rcases hadj with hd | hd
  · rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact False.elim (hne1 h)
    · exact False.elim (hne2 h)
  · obtain ⟨m, hm⟩ := hd
    have hp := Foundation.term_pos J hJ (lastIndex J - 1) hi
    constructor
    · change Even (term J (lastIndex J - 1))
      exact ⟨m, by omega⟩
    · omega

theorem DivisorGraphRuleH.Shortening.firstEvenIndex_eq_some_iff (J : List ℕ) (k : ℕ) :
    DivisorGraphRuleH.firstEvenIndex J = some k ↔ DivisorGraphRuleH.FirstEven J k := by
  simp [firstEvenIndex, FirstEven, and_comm, and_left_comm, and_assoc]

theorem DivisorGraphRuleH.Shortening.firstEvenIndex_le (J : List ℕ) (j : ℕ) (hj : j < J.length) (hej : DivisorGraphRuleH.e J j) :
    ∃ k : ℕ, DivisorGraphRuleH.FirstEven J k ∧ DivisorGraphRuleH.firstEvenIndex J = some k ∧ k ≤ j := by
  cases hf : firstEvenIndex J with
  | none =>
    simp only [firstEvenIndex, List.find?_eq_none, List.mem_range, decide_eq_true_eq] at hf
    exact False.elim (hf j hj hej)
  | some k =>
    have hfirst := (Shortening.firstEvenIndex_eq_some_iff J k).mp hf
    refine ⟨k, hfirst, rfl, ?_⟩
    by_contra hle
    exact hfirst.2.2 j (by omega) hej

theorem DivisorGraphRuleH.Shortening.firstEven_bounds (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J)
    (hn : 2 ≤ DivisorGraphRuleH.lastIndex J) (hodd : Odd (DivisorGraphRuleH.term J 1)) :
    ∃ k : ℕ, DivisorGraphRuleH.FirstEven J k ∧ 2 ≤ k ∧ k ≤ DivisorGraphRuleH.lastIndex J - 1 ∧
      DivisorGraphRuleH.firstEvenIndex J = some k := by
  have hb := Foundation.lastIndex_bounds J hJ
  obtain ⟨k, hf, hfind, hkle⟩ := Shortening.firstEvenIndex_le J (lastIndex J - 1)
    (by omega) (R0 J hJ hn).1
  have hn0 : ¬ e J 0 := by
    change ¬ Even (term J 0)
    rw [Foundation.term_first J hJ]
    decide
  have hn1 : ¬ e J 1 := Nat.not_even_iff_odd.mpr hodd
  have hk0 : k ≠ 0 := by
    intro hk
    exact hn0 (hk ▸ hf.2.1)
  have hk1 : k ≠ 1 := by
    intro hk
    exact hn1 (hk ▸ hf.2.1)
  exact ⟨k, hf, by omega, hkle, hfind⟩

theorem DivisorGraphRuleH.Shortening.suffix_preservation (J : List ℕ) (s : ℤ) (hJ : DivisorGraphRuleH.TablePathAt J s)
    (k : ℕ) (hk : 1 ≤ k) (hkLast : k < DivisorGraphRuleH.lastIndex J) :
    DivisorGraphRuleH.TablePathAt (1 :: J.drop k) s ∧ 3 ≤ (1 :: J.drop k).length ∧
      (∀ c ∈ (1 :: J.drop k), c ∈ J) ∧
      DivisorGraphRuleH.term (1 :: J.drop k) 1 = DivisorGraphRuleH.term J k ∧
      (1 :: J.drop k).drop 1 = J.drop k := by
  have hb := Foundation.lastIndex_bounds J hJ.1
  have hlen : 2 ≤ (J.drop k).length := by
    rw [List.length_drop]
    omega
  have hne : J.drop k ≠ [] := by
    intro he
    rw [he] at hlen
    simp at hlen
  have hsl : List.Sublist (1 :: J.drop k) J := by
    obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp hJ.1.2.1
    cases k with
    | zero => omega
    | succ k =>
      change List.Sublist (1 :: tail.drop k) (1 :: tail)
      exact List.cons_sublist_cons.mpr (List.drop_sublist k tail)
  have hsub : ∀ c ∈ (1 :: J.drop k), c ∈ J := hsl.subset
  have hpos : ∀ c ∈ (1 :: J.drop k), 0 < c := by
    intro c hc
    exact hJ.1.1.1 c (hsub c hc)
  have hnodup : (1 :: J.drop k).Nodup := List.Nodup.sublist hsl hJ.1.1.2.1
  have hchain : (1 :: J.drop k).IsChain Comparable := by
    apply List.isChain_cons.mpr
    refine ⟨?_, hJ.1.1.2.2.drop k⟩
    intro y hy
    exact Or.inl (one_dvd y)
  have hlast : (1 :: J.drop k).getLast? = some 2 := by
    rw [List.getLast?_cons_of_ne_nil hne, List.getLast?_drop, if_neg (by omega)]
    exact hJ.1.2.2
  have hsecond : term (1 :: J.drop k) 1 = term J k := by
    rw [Foundation.term_getElem (1 :: J.drop k) 1 (by simp only [List.length_cons]; omega),
      Foundation.term_getElem J k (by omega)]
    simp only [List.getElem_cons_succ, List.getElem_drop, Nat.add_zero]
  refine ⟨⟨⟨⟨hpos, hnodup, hchain⟩, rfl, hlast⟩, ?_⟩, ?_, hsub, hsecond, rfl⟩
  · intro c hc
    exact hJ.2 c (hsub c hc)
  · simp only [List.length_cons]
    omega

theorem DivisorGraphRuleH.Shortening.no_three_entry_odd_second (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) (hlen : J.length = 3) :
    ¬ Odd (DivisorGraphRuleH.term J 1) := by
  have hn : lastIndex J = 2 := by simp only [lastIndex, hlen]
  have hev := (R0 J hJ (by omega)).1
  have hsecond : Even (term J 1) := by simpa only [e, hn] using hev
  intro ho
  exact (Nat.not_even_iff_odd.mpr ho) hsecond

theorem DivisorGraphRuleH.H2 (J : List ℕ) (s : ℤ) (hJ : TablePathAt J s)
    (hn : 2 ≤ lastIndex J) (hodd : Odd (term J 1)) :
    ∃ k : ℕ, FirstEven J k ∧ 2 ≤ k ∧ k ≤ lastIndex J - 1 ∧
      shortenedPath J = some (1 :: J.drop k) ∧
      TablePathAt (1 :: J.drop k) s ∧
      3 ≤ (1 :: J.drop k).length ∧
      (∀ c ∈ (1 :: J.drop k), c ∈ J) ∧ e (1 :: J.drop k) 1 := by
  obtain ⟨k, hf, hklo, hkhi, hfind⟩ := Shortening.firstEven_bounds J hJ.1 hn hodd
  have hkLast : k < lastIndex J := by omega
  obtain ⟨htab, hlen, hsub, hsecond, hsuffix⟩ :=
    Shortening.suffix_preservation J s hJ k (by omega) hkLast
  have hn1 : ¬ e J 1 := Nat.not_even_iff_odd.mpr hodd
  refine ⟨k, hf, hklo, hkhi, ?_, htab, hlen, hsub, ?_⟩
  · have hbranch : 2 ≤ lastIndex J ∧ ¬ e J 1 := ⟨hn, hn1⟩
    rw [shortenedPath, if_pos hbranch, hfind]
    rfl
  · change Even (term (1 :: J.drop k) 1)
    rw [hsecond]
    exact hf.2.1

def DivisorGraphRuleH.Shortening.results : Unit := ()
