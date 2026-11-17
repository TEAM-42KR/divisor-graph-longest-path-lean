import Mathlib
import RuleHRelease.Definitions.Foundation
set_option autoImplicit false
open DivisorGraphRuleH

theorem DivisorGraphRuleH.IndexWords.down_perm_up (hi lo : ℕ) : (DivisorGraphRuleH.down hi lo).Perm (DivisorGraphRuleH.up lo hi) := by
  change (up lo hi).reverse.Perm (up lo hi)
  exact List.reverse_perm _

theorem DivisorGraphRuleH.IndexWords.up_zero_range (n : ℕ) : DivisorGraphRuleH.up 0 n = List.range (n + 1) := by
  simpa only [DivisorGraphRuleH.up, Nat.sub_zero] using (List.range_eq_range' (n := n + 1)).symm

theorem DivisorGraphRuleH.IndexWords.up_split (lo mid hi : ℕ) (hl : lo ≤ mid + 1) (hh : mid ≤ hi) :
    DivisorGraphRuleH.up lo hi = DivisorGraphRuleH.up lo mid ++ DivisorGraphRuleH.up (mid + 1) hi := by
  have hs : lo + (mid + 1 - lo) = mid + 1 := by omega
  have hn : (mid + 1 - lo) + (hi + 1 - (mid + 1)) = hi + 1 - lo := by omega
  unfold up
  calc
    List.range' lo (hi + 1 - lo) =
        List.range' lo ((mid + 1 - lo) + (hi + 1 - (mid + 1))) := by rw [hn]
    _ = _ := by rw [← List.range'_append_1, hs]

theorem DivisorGraphRuleH.IndexWords.interval_perm_iff (W : List ℕ) (lo hi : ℕ) :
    W.Perm (DivisorGraphRuleH.up lo hi) ↔
      W.Nodup ∧ ∀ i : ℕ, i ∈ W ↔ lo ≤ i ∧ i ≤ hi := by
  constructor
  · intro h
    exact ⟨h.nodup_iff.mpr (DivisorGraphRuleH.Foundation.up_nodup lo hi),
      fun i => h.mem_iff.trans (DivisorGraphRuleH.Foundation.mem_up lo hi i)⟩
  · rintro ⟨hnd, hc⟩
    apply (List.perm_ext_iff_of_nodup hnd (DivisorGraphRuleH.Foundation.up_nodup lo hi)).2
    intro i
    exact (hc i).trans (DivisorGraphRuleH.Foundation.mem_up lo hi i).symm

theorem DivisorGraphRuleH.IndexWords.interval_disjoint (A B : List ℕ) (a b c d : ℕ)
    (hA : A.Perm (DivisorGraphRuleH.up a b)) (hB : B.Perm (DivisorGraphRuleH.up c d))
    (hsep : b < c ∨ d < a) : List.Disjoint A B := by
  rw [List.disjoint_left]
  intro i hiA hiB
  have ha := (DivisorGraphRuleH.Foundation.mem_up a b i).1 (hA.mem_iff.1 hiA)
  have hb := (DivisorGraphRuleH.Foundation.mem_up c d i).1 (hB.mem_iff.1 hiB)
  rcases hsep with h | h <;> omega

theorem DivisorGraphRuleH.IndexWords.append_blocks_perm (A B : List ℕ) (lo mid hi : ℕ) (hl : lo ≤ mid + 1) (hh : mid ≤ hi)
    (hA : A.Perm (DivisorGraphRuleH.up lo mid))
    (hB : B.Perm (DivisorGraphRuleH.up (mid + 1) hi)) :
    (A ++ B).Perm (DivisorGraphRuleH.up lo hi) := by
  rw [DivisorGraphRuleH.IndexWords.up_split lo mid hi hl hh]
  exact hA.append hB

theorem DivisorGraphRuleH.IndexWords.range_perm_iff (W : List ℕ) (n : ℕ) :
    W.Perm (List.range (n + 1)) ↔ W.Nodup ∧ ∀ i : ℕ, i ∈ W ↔ i ≤ n := by
  rw [← DivisorGraphRuleH.IndexWords.up_zero_range n, DivisorGraphRuleH.IndexWords.interval_perm_iff]
  simp only [Nat.zero_le, true_and]

theorem DivisorGraphRuleH.IndexWords.zero_positive_perm (W : List ℕ) (n : ℕ) (hW : W.Perm (DivisorGraphRuleH.up 1 n)) :
    ([0] ++ W).Perm (List.range (n + 1)) := by
  rw [← DivisorGraphRuleH.IndexWords.up_zero_range n]
  apply DivisorGraphRuleH.IndexWords.append_blocks_perm [0] W 0 0 n (by omega) (by omega)
  · simp [up, List.range']
  · exact hW

theorem DivisorGraphRuleH.IndexWords.two_positive_blocks_perm (A B : List ℕ) (k n : ℕ) (hk : 1 ≤ k) (hn : k ≤ n)
    (hA : A.Perm (DivisorGraphRuleH.up 1 k))
    (hB : B.Perm (DivisorGraphRuleH.up (k + 1) n)) :
    (A ++ [0] ++ B).Perm (List.range (n + 1)) := by
  have hp := DivisorGraphRuleH.IndexWords.append_blocks_perm A B 1 k n (by omega) hn hA hB
  have hz := DivisorGraphRuleH.IndexWords.zero_positive_perm (A ++ B) n hp
  have hs0 : (A ++ [0]).Perm ([0] ++ A) := List.perm_append_comm
  have hs : (A ++ [0] ++ B).Perm ([0] ++ (A ++ B)) := by
    simpa only [List.append_assoc] using hs0.append_right B
  exact hs.trans hz

theorem DivisorGraphRuleH.IndexWords.three_positive_blocks_perm (A B C : List ℕ) (u w n : ℕ) (hu : 1 ≤ u) (huw : u < w) (hwn : w ≤ n)
    (hA : A.Perm (DivisorGraphRuleH.up 1 u))
    (hB : B.Perm (DivisorGraphRuleH.up (u + 1) (w - 1)))
    (hC : C.Perm (DivisorGraphRuleH.up w n)) :
    (A ++ [0] ++ B ++ C).Perm (List.range (n + 1)) := by
  have hw : w - 1 + 1 = w := by omega
  have hBC : (B ++ C).Perm (up (u + 1) n) := by
    apply DivisorGraphRuleH.IndexWords.append_blocks_perm B C (u + 1) (w - 1) n (by omega) (by omega) hB
    simpa only [hw] using hC
  simpa only [List.append_assoc] using
    DivisorGraphRuleH.IndexWords.two_positive_blocks_perm A (B ++ C) u n hu (by omega) hA hBC

theorem DivisorGraphRuleH.IndexWords.comparable_symm (a b : ℕ) (h : DivisorGraphRuleH.Comparable a b) : DivisorGraphRuleH.Comparable b a := by
  exact h.elim Or.inr Or.inl

theorem DivisorGraphRuleH.IndexWords.index_step (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) (i j : ℕ)
    (hi : i < J.length) (hj : j < J.length) (hstep : i + 1 = j ∨ j + 1 = i) :
    DivisorGraphRuleH.Comparable (DivisorGraphRuleH.term J i) (DivisorGraphRuleH.term J j) := by
  rcases hstep with h | h
  · subst j
    exact DivisorGraphRuleH.Foundation.term_adjacent J hJ i hj
  · subst i
    exact DivisorGraphRuleH.IndexWords.comparable_symm _ _ (DivisorGraphRuleH.Foundation.term_adjacent J hJ j hi)

theorem DivisorGraphRuleH.IndexWords.zero_junction (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) (i : ℕ) :
    DivisorGraphRuleH.Comparable (DivisorGraphRuleH.term J 0) (DivisorGraphRuleH.term J i) ∧
    DivisorGraphRuleH.Comparable (DivisorGraphRuleH.term J i) (DivisorGraphRuleH.term J 0) := by
  have hf : Comparable (term J 0) (term J i) := by
    rw [DivisorGraphRuleH.Foundation.term_first J hJ]
    exact Or.inl (one_dvd _)
  exact ⟨hf, DivisorGraphRuleH.IndexWords.comparable_symm _ _ hf⟩

theorem DivisorGraphRuleH.IndexWords.even_junction (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) (i : ℕ) (he : DivisorGraphRuleH.e J i) :
    DivisorGraphRuleH.Comparable (DivisorGraphRuleH.term J (DivisorGraphRuleH.lastIndex J)) (DivisorGraphRuleH.term J i) ∧
    DivisorGraphRuleH.Comparable (DivisorGraphRuleH.term J i) (DivisorGraphRuleH.term J (DivisorGraphRuleH.lastIndex J)) := by
  have hf : Comparable (term J (lastIndex J)) (term J i) := by
    rw [DivisorGraphRuleH.Foundation.term_last J hJ]
    exact Or.inl ((show Even (term J i) from he).two_dvd)
  exact ⟨hf, DivisorGraphRuleH.IndexWords.comparable_symm _ _ hf⟩

theorem DivisorGraphRuleH.IndexWords.up_chain (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) (lo hi : ℕ) (hh : hi < J.length) :
    (DivisorGraphRuleH.up lo hi).IsChain
      (fun i j => DivisorGraphRuleH.Comparable (DivisorGraphRuleH.term J i) (DivisorGraphRuleH.term J j)) := by
  apply List.isChain_iff_getElem.mpr
  intro i hi'
  have hb : i + 1 < hi + 1 - lo := by
    simpa only [DivisorGraphRuleH.Foundation.up_length] using hi'
  rw [DivisorGraphRuleH.Foundation.up_getElem lo hi i (by omega),
      DivisorGraphRuleH.Foundation.up_getElem lo hi (i + 1) hi']
  simpa only [Nat.add_assoc] using
    DivisorGraphRuleH.Foundation.term_adjacent J hJ (lo + i) (by omega)

theorem DivisorGraphRuleH.IndexWords.reverse_chain (J W : List ℕ)
    (hW : W.IsChain (fun i j => DivisorGraphRuleH.Comparable (DivisorGraphRuleH.term J i) (DivisorGraphRuleH.term J j))) :
    W.reverse.IsChain (fun i j => DivisorGraphRuleH.Comparable (DivisorGraphRuleH.term J i) (DivisorGraphRuleH.term J j)) := by
  apply List.isChain_reverse.mpr
  exact hW.imp_of_mem_imp (fun i j _ _ hij => DivisorGraphRuleH.IndexWords.comparable_symm _ _ hij)

theorem DivisorGraphRuleH.IndexWords.down_chain (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) (hi lo : ℕ) (hh : hi < J.length) :
    (DivisorGraphRuleH.down hi lo).IsChain
      (fun i j => DivisorGraphRuleH.Comparable (DivisorGraphRuleH.term J i) (DivisorGraphRuleH.term J j)) := by
  change (up lo hi).reverse.IsChain _
  exact DivisorGraphRuleH.IndexWords.reverse_chain J (up lo hi) (DivisorGraphRuleH.IndexWords.up_chain J hJ lo hi hh)

theorem DivisorGraphRuleH.IndexWords.chain_append_endpoints (J A B : List ℕ) (a b : ℕ)
    (hA : A.IsChain (fun i j => DivisorGraphRuleH.Comparable (DivisorGraphRuleH.term J i) (DivisorGraphRuleH.term J j)))
    (hB : B.IsChain (fun i j => DivisorGraphRuleH.Comparable (DivisorGraphRuleH.term J i) (DivisorGraphRuleH.term J j)))
    (ha : A.getLast? = some a) (hb : B.head? = some b)
    (hab : DivisorGraphRuleH.Comparable (DivisorGraphRuleH.term J a) (DivisorGraphRuleH.term J b)) :
    (A ++ B).IsChain (fun i j => DivisorGraphRuleH.Comparable (DivisorGraphRuleH.term J i) (DivisorGraphRuleH.term J j)) := by
  apply hA.append hB
  intro x hx y hy
  simp only [ha, Option.mem_some_iff] at hx
  simp only [hb, Option.mem_some_iff] at hy
  subst x
  subst y
  exact hab

theorem DivisorGraphRuleH.IndexWords.zero_stitch (J : List ℕ) (hJ : DivisorGraphRuleH.TablePath J) (A B : List ℕ)
    (hA : A.IsChain (fun i j => DivisorGraphRuleH.Comparable (DivisorGraphRuleH.term J i) (DivisorGraphRuleH.term J j)))
    (hB : B.IsChain (fun i j => DivisorGraphRuleH.Comparable (DivisorGraphRuleH.term J i) (DivisorGraphRuleH.term J j))) :
    (A ++ [0] ++ B).IsChain (fun i j => DivisorGraphRuleH.Comparable (DivisorGraphRuleH.term J i) (DivisorGraphRuleH.term J j)) := by
  have h0 : ([0] : List ℕ).IsChain
      (fun i j => Comparable (term J i) (term J j)) := List.isChain_singleton 0
  have hA0 := hA.append h0 (by
    intro x hx y hy
    have hy0 : 0 = y := by simpa using hy
    subst y
    exact (DivisorGraphRuleH.IndexWords.zero_junction J hJ x).2)
  apply hA0.append hB
  intro x hx y hy
  have hx0 : 0 = x := by simpa using hx
  subst x
  exact (DivisorGraphRuleH.IndexWords.zero_junction J hJ y).1

theorem DivisorGraphRuleH.IndexWords.append_endpoints (A B : List ℕ) (a b : ℕ) (ha : A.head? = some a) (hb : B.getLast? = some b) :
    (A ++ B).head? = some a ∧ (A ++ B).getLast? = some b := by
  aesop

def DivisorGraphRuleH.IndexWords.results : Unit := ()
