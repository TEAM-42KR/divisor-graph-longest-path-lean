import Mathlib
import RuleHRelease.Definitions.Shortening
import RuleHRelease.Definitions.RouteExistence
set_option autoImplicit false

def DivisorGraphRuleH.Offers.results : Prop := True

theorem DivisorGraphRuleH.Offers.direct_exists (J : List ℕ) (s : ℤ) (hJ : DivisorGraphRuleH.TablePathAt J s)
    (he : DivisorGraphRuleH.e J 1) (slot : DivisorGraphRuleH.Slot)
    (hslot : slot.Valid) (hsize : (slot.size : ℤ) ≤ s) :
    ∃ B : DivisorGraphRuleH.TableBlock, DivisorGraphRuleH.directBlock J s slot = some B := by
  obtain ⟨r, hr⟩ := (DivisorGraphRuleH.H4 J s hJ he).2 slot hslot hsize
  refine ⟨⟨J, r⟩, ?_⟩
  change DivisorGraphRuleH.selectedRoute J s slot = some r at hr
  simp only [DivisorGraphRuleH.directBlock, hr, Option.map_some]

theorem DivisorGraphRuleH.Offers.direct_or_short (J : List ℕ) (s : ℤ) (hJ : DivisorGraphRuleH.TablePathAt J s)
    (slot : DivisorGraphRuleH.Slot) (hslot : slot.Valid) (hsize : (slot.size : ℤ) ≤ s) :
    (∃ B : DivisorGraphRuleH.TableBlock, DivisorGraphRuleH.directBlock J s slot = some B) ∨
    (∃ A : DivisorGraphRuleH.TableBlock, DivisorGraphRuleH.shortBlock J s slot = some A) := by
  by_cases he : DivisorGraphRuleH.e J 1
  · exact Or.inl (DivisorGraphRuleH.Offers.direct_exists J s hJ he slot hslot hsize)
  · have hlen : 2 ≤ J.length := DivisorGraphRuleH.Foundation.tablePath_length J hJ.1
    have hlast : DivisorGraphRuleH.term J (DivisorGraphRuleH.lastIndex J) = 2 :=
      DivisorGraphRuleH.Foundation.term_last J hJ.1
    have hne : DivisorGraphRuleH.lastIndex J ≠ 1 := by
      intro h
      apply he
      change Even (DivisorGraphRuleH.term J 1)
      rw [← h, hlast]
      decide
    have hn : 2 ≤ DivisorGraphRuleH.lastIndex J := by
      unfold DivisorGraphRuleH.lastIndex at *
      omega
    have hodd : Odd (DivisorGraphRuleH.term J 1) := Nat.not_even_iff_odd.mp he
    obtain ⟨k, _, _, _, hshort, hK, _, _, heK⟩ :=
      DivisorGraphRuleH.H2 J s hJ hn hodd
    obtain ⟨A, hA⟩ := DivisorGraphRuleH.Offers.direct_exists (1 :: J.drop k) s hK heK
      slot hslot hsize
    exact Or.inr ⟨A, by simp only [DivisorGraphRuleH.shortBlock, hshort, Option.bind_some, hA]⟩

theorem DivisorGraphRuleH.Offers.firstB_cons (I : List ℕ) (pool : List (List ℕ)) (s : ℤ) (slot : DivisorGraphRuleH.Slot) :
    DivisorGraphRuleH.firstB (I :: pool) s slot =
      match DivisorGraphRuleH.directBlock I s slot with
      | some B => some B
      | none => DivisorGraphRuleH.firstB pool s slot := by
  unfold DivisorGraphRuleH.firstB
  rw [List.findSome?_cons]
  cases DivisorGraphRuleH.directBlock I s slot <;> rfl

theorem DivisorGraphRuleH.Offers.beforeB_cons (I : List ℕ) (pool : List (List ℕ)) (s : ℤ) (slot : DivisorGraphRuleH.Slot) :
    DivisorGraphRuleH.beforeB (I :: pool) s slot =
      if (DivisorGraphRuleH.selectedRoute I s slot).isNone then
        I :: DivisorGraphRuleH.beforeB pool s slot else [] := by
  simp only [DivisorGraphRuleH.beforeB, List.takeWhile_cons]

theorem DivisorGraphRuleH.Offers.firstA_cons (I : List ℕ) (pool : List (List ℕ)) (s : ℤ) (slot : DivisorGraphRuleH.Slot) :
    DivisorGraphRuleH.firstA (I :: pool) s slot =
      if (DivisorGraphRuleH.selectedRoute I s slot).isNone then
        match DivisorGraphRuleH.shortBlock I s slot with
        | some A => some A
        | none => DivisorGraphRuleH.firstA pool s slot
      else none := by
  unfold DivisorGraphRuleH.firstA
  rw [DivisorGraphRuleH.Offers.beforeB_cons]
  split
  · rw [List.findSome?_cons]
    cases DivisorGraphRuleH.shortBlock I s slot <;> rfl
  · simp only [List.findSome?_nil]

theorem DivisorGraphRuleH.Offers.candidate_exists (pool : List (List ℕ)) (s : ℤ)
    (hnonempty : pool ≠ []) (hpool : ∀ J ∈ pool, DivisorGraphRuleH.TablePathAt J s)
    (slot : DivisorGraphRuleH.Slot) (hslot : slot.Valid) (hsize : (slot.size : ℤ) ≤ s) :
    (∃ A : DivisorGraphRuleH.TableBlock, DivisorGraphRuleH.firstA pool s slot = some A) ∨
    (∃ B : DivisorGraphRuleH.TableBlock, DivisorGraphRuleH.firstB pool s slot = some B) := by
  cases pool with
  | nil => exact False.elim (hnonempty rfl)
  | cons I rest =>
    have hI : DivisorGraphRuleH.TablePathAt I s := hpool I List.mem_cons_self
    cases hD : DivisorGraphRuleH.directBlock I s slot with
    | some B =>
      exact Or.inr ⟨B, by rw [DivisorGraphRuleH.Offers.firstB_cons, hD]⟩
    | none =>
      obtain hdir | ⟨A, hA⟩ :=
        DivisorGraphRuleH.Offers.direct_or_short I s hI slot hslot hsize
      · obtain ⟨B, hB⟩ := hdir
        rw [hD] at hB
        contradiction
      · have hroute : DivisorGraphRuleH.selectedRoute I s slot = none := by
          cases hr : DivisorGraphRuleH.selectedRoute I s slot with
          | none => rfl
          | some r => simp [DivisorGraphRuleH.directBlock, hr] at hD
        exact Or.inl ⟨A, by rw [DivisorGraphRuleH.Offers.firstA_cons, hroute]; simp only [Option.isNone_none, ite_true, hA]⟩

theorem DivisorGraphRuleH.Offers.offer_exists_iff (pool : List (List ℕ)) (s : ℤ) (slot : DivisorGraphRuleH.Slot) :
    (∃ block : DivisorGraphRuleH.TableBlock, DivisorGraphRuleH.offer pool s slot = some block) ↔
    (∃ A : DivisorGraphRuleH.TableBlock, DivisorGraphRuleH.firstA pool s slot = some A) ∨
    (∃ B : DivisorGraphRuleH.TableBlock, DivisorGraphRuleH.firstB pool s slot = some B) := by
  cases hA : DivisorGraphRuleH.firstA pool s slot with
  | none =>
    cases hB : DivisorGraphRuleH.firstB pool s slot with
    | none => simp [DivisorGraphRuleH.offer, hA, hB]
    | some B => simp [DivisorGraphRuleH.offer, hA, hB]
  | some A =>
    cases hB : DivisorGraphRuleH.firstB pool s slot with
    | none => simp [DivisorGraphRuleH.offer, hA, hB]
    | some B =>
      by_cases hgain : DivisorGraphRuleH.gain B.inner B.route ≤ DivisorGraphRuleH.gain A.inner A.route
      · simp [DivisorGraphRuleH.offer, hA, hB, hgain]
      · simp [DivisorGraphRuleH.offer, hA, hB, hgain]

theorem DivisorGraphRuleH.Offers.offer_gain_tie (pool : List (List ℕ)) (s : ℤ) (slot : DivisorGraphRuleH.Slot)
    (A B : DivisorGraphRuleH.TableBlock)
    (hA : DivisorGraphRuleH.firstA pool s slot = some A)
    (hB : DivisorGraphRuleH.firstB pool s slot = some B)
    (hgain : DivisorGraphRuleH.gain A.inner A.route = DivisorGraphRuleH.gain B.inner B.route) :
    DivisorGraphRuleH.offer pool s slot = some A := by
  simp only [DivisorGraphRuleH.offer, hA, hB, hgain, le_refl, ite_true]

theorem DivisorGraphRuleH.H5 (pool : List (List ℕ)) (s : ℤ)
    (hnonempty : pool ≠ []) (hpool : ∀ J ∈ pool, DivisorGraphRuleH.TablePathAt J s)
    (slot : DivisorGraphRuleH.Slot) (hslot : slot.Valid) (hsize : (slot.size : ℤ) ≤ s) :
    ∃ block : DivisorGraphRuleH.TableBlock, DivisorGraphRuleH.offer pool s slot = some block := by
  exact (DivisorGraphRuleH.Offers.offer_exists_iff pool s slot).2
    (DivisorGraphRuleH.Offers.candidate_exists pool s hnonempty hpool slot hslot hsize)
