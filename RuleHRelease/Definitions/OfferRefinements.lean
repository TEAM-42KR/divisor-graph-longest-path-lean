import Mathlib
import RuleHRelease.Definitions.ExecutableDirectoryIndices
set_option autoImplicit false

theorem DivisorGraphRuleH.OfferRefinements.directBlock_eq : DivisorGraphRuleH.Exec.directBlock = DivisorGraphRuleH.directBlock := by
  funext J s slot
  unfold DivisorGraphRuleH.Exec.directBlock DivisorGraphRuleH.directBlock
  rw [DivisorGraphRuleH.SequenceRefinements.selectedRoute_eq]

theorem DivisorGraphRuleH.OfferRefinements.shortBlock_eq : DivisorGraphRuleH.Exec.shortBlock = DivisorGraphRuleH.shortBlock := by
  funext I s slot
  unfold DivisorGraphRuleH.Exec.shortBlock DivisorGraphRuleH.shortBlock
  rw [DivisorGraphRuleH.SequenceRefinements.shortenedPath_eq, DivisorGraphRuleH.OfferRefinements.directBlock_eq]

theorem DivisorGraphRuleH.OfferRefinements.firstB_eq : DivisorGraphRuleH.Exec.firstB = DivisorGraphRuleH.firstB := by
  funext pool s slot
  unfold DivisorGraphRuleH.Exec.firstB DivisorGraphRuleH.firstB
  rw [DivisorGraphRuleH.OfferRefinements.directBlock_eq]

theorem DivisorGraphRuleH.OfferRefinements.beforeB_eq : DivisorGraphRuleH.Exec.beforeB = DivisorGraphRuleH.beforeB := by
  funext pool s slot
  unfold DivisorGraphRuleH.Exec.beforeB DivisorGraphRuleH.beforeB
  rw [DivisorGraphRuleH.SequenceRefinements.selectedRoute_eq]

theorem DivisorGraphRuleH.OfferRefinements.firstA_eq : DivisorGraphRuleH.Exec.firstA = DivisorGraphRuleH.firstA := by
  funext pool s slot
  unfold DivisorGraphRuleH.Exec.firstA DivisorGraphRuleH.firstA
  rw [DivisorGraphRuleH.OfferRefinements.beforeB_eq, DivisorGraphRuleH.OfferRefinements.shortBlock_eq]

theorem DivisorGraphRuleH.OfferRefinements.offerExec_eq : DivisorGraphRuleH.Exec.offerExec = DivisorGraphRuleH.offer := by
  funext pool s slot
  unfold DivisorGraphRuleH.Exec.offerExec DivisorGraphRuleH.Exec.chooseBlock DivisorGraphRuleH.offer
  rw [DivisorGraphRuleH.OfferRefinements.firstA_eq, DivisorGraphRuleH.OfferRefinements.firstB_eq,
    DivisorGraphRuleH.SequenceRefinements.gain_eq]
  all_goals rfl

theorem DivisorGraphRuleH.OfferRefinements.taggedFindSome_project (f : List ℕ → Option DivisorGraphRuleH.TableBlock) (flag : Bool) (offset : ℕ) (pool : List (List ℕ)) : (DivisorGraphRuleH.Exec.taggedFindSome f flag offset pool).map DivisorGraphRuleH.Exec.OfferTrace.block = pool.findSome? f := by
  induction pool generalizing offset with
  | nil => rfl
  | cons J rest ih =>
    cases hf : f J with
    | none => simpa only [DivisorGraphRuleH.Exec.taggedFindSome, hf, List.findSome?_cons] using ih (offset + 1)
    | some block => simp [DivisorGraphRuleH.Exec.taggedFindSome, hf]

theorem DivisorGraphRuleH.OfferRefinements.firstBTrace_project (pool : List (List ℕ)) (s : ℤ) (slot : DivisorGraphRuleH.Slot) : (DivisorGraphRuleH.Exec.firstBTrace pool s slot).map DivisorGraphRuleH.Exec.OfferTrace.block = DivisorGraphRuleH.firstB pool s slot := by
  unfold DivisorGraphRuleH.Exec.firstBTrace
  rw [DivisorGraphRuleH.OfferRefinements.taggedFindSome_project]
  change DivisorGraphRuleH.Exec.firstB pool s slot = _
  rw [DivisorGraphRuleH.OfferRefinements.firstB_eq]

theorem DivisorGraphRuleH.OfferRefinements.firstATrace_project (pool : List (List ℕ)) (s : ℤ) (slot : DivisorGraphRuleH.Slot) : (DivisorGraphRuleH.Exec.firstATrace pool s slot).map DivisorGraphRuleH.Exec.OfferTrace.block = DivisorGraphRuleH.firstA pool s slot := by
  unfold DivisorGraphRuleH.Exec.firstATrace
  rw [DivisorGraphRuleH.OfferRefinements.taggedFindSome_project]
  change DivisorGraphRuleH.Exec.firstA pool s slot = _
  rw [DivisorGraphRuleH.OfferRefinements.firstA_eq]

theorem DivisorGraphRuleH.OfferRefinements.chooseTrace_project (A B : Option DivisorGraphRuleH.Exec.OfferTrace) : (DivisorGraphRuleH.Exec.chooseTrace A B).map DivisorGraphRuleH.Exec.OfferTrace.block = DivisorGraphRuleH.Exec.chooseBlock (A.map DivisorGraphRuleH.Exec.OfferTrace.block) (B.map DivisorGraphRuleH.Exec.OfferTrace.block) := by
  cases A <;> cases B <;>
    simp [DivisorGraphRuleH.Exec.chooseTrace, DivisorGraphRuleH.Exec.chooseBlock]
  split <;> rfl

theorem DivisorGraphRuleH.OfferRefinements.offerTrace_project (pool : List (List ℕ)) (s : ℤ) (slot : DivisorGraphRuleH.Slot) : (DivisorGraphRuleH.Exec.offerTrace pool s slot).map DivisorGraphRuleH.Exec.OfferTrace.block = DivisorGraphRuleH.offer pool s slot := by
  unfold DivisorGraphRuleH.Exec.offerTrace
  rw [DivisorGraphRuleH.OfferRefinements.chooseTrace_project,
    DivisorGraphRuleH.OfferRefinements.firstATrace_project, DivisorGraphRuleH.OfferRefinements.firstBTrace_project]
  unfold DivisorGraphRuleH.Exec.chooseBlock DivisorGraphRuleH.offer
  rw [DivisorGraphRuleH.SequenceRefinements.gain_eq]
  all_goals rfl

theorem DivisorGraphRuleH.OfferRefinements.taggedFindSome_spec (f : List ℕ → Option DivisorGraphRuleH.TableBlock) (flag : Bool) (offset : ℕ) (pool : List (List ℕ)) (t : DivisorGraphRuleH.Exec.OfferTrace) (h : DivisorGraphRuleH.Exec.taggedFindSome f flag offset pool = some t) : ∃ pre I post, pool = pre ++ I :: post ∧ t.poolIndex = offset + pre.length ∧ t.shortened = flag ∧ f I = some t.block ∧ ∀ J ∈ pre, f J = none := by
  induction pool generalizing offset with
  | nil => simp [DivisorGraphRuleH.Exec.taggedFindSome] at h
  | cons J rest ih =>
    cases hf : f J with
    | none =>
      have ht : DivisorGraphRuleH.Exec.taggedFindSome f flag (offset + 1) rest = some t := by
        simpa only [DivisorGraphRuleH.Exec.taggedFindSome, hf] using h
      obtain ⟨pre, I, post, hp, hi, hb, hI, hpre⟩ := ih (offset + 1) ht
      refine ⟨J :: pre, I, post, ?_, ?_, hb, hI, ?_⟩
      · simp only [hp, List.cons_append]
      · simp only [List.length_cons]
        omega
      · intro K hK
        rcases List.mem_cons.mp hK with hK | hK
        · simpa only [hK] using hf
        · exact hpre K hK
    | some block =>
      have ht : (⟨offset, flag, block⟩ : DivisorGraphRuleH.Exec.OfferTrace) = t := by
        simpa only [DivisorGraphRuleH.Exec.taggedFindSome, hf, Option.some.injEq] using h
      subst t
      exact ⟨[], J, rest, rfl, by simp, rfl, hf, by simp⟩

theorem DivisorGraphRuleH.OfferRefinements.firstB_prefix_length (pool : List (List ℕ)) (s : ℤ) (slot : DivisorGraphRuleH.Slot) (offset : ℕ) (t : DivisorGraphRuleH.Exec.OfferTrace) (h : DivisorGraphRuleH.Exec.taggedFindSome (fun J => DivisorGraphRuleH.Exec.directBlock J s slot) false offset pool = some t) : (DivisorGraphRuleH.Exec.beforeB pool s slot).length + offset = t.poolIndex := by
  induction pool generalizing offset with
  | nil => simp [DivisorGraphRuleH.Exec.taggedFindSome] at h
  | cons I rest ih =>
    cases hr : DivisorGraphRuleH.Exec.selectedRoute I s slot with
    | none =>
      have ht : DivisorGraphRuleH.Exec.taggedFindSome
          (fun J => DivisorGraphRuleH.Exec.directBlock J s slot) false (offset + 1) rest = some t := by
        simpa only [DivisorGraphRuleH.Exec.taggedFindSome, DivisorGraphRuleH.Exec.directBlock,
          hr, Option.map_none] using h
      have hh := ih (offset + 1) ht
      have hb : DivisorGraphRuleH.Exec.beforeB (I :: rest) s slot =
          I :: DivisorGraphRuleH.Exec.beforeB rest s slot := by
        simp [DivisorGraphRuleH.Exec.beforeB, hr]
      rw [hb, List.length_cons]
      omega
    | some r =>
      have ht : (⟨offset, false, ⟨I, r⟩⟩ : DivisorGraphRuleH.Exec.OfferTrace) = t := by
        simpa [DivisorGraphRuleH.Exec.taggedFindSome, DivisorGraphRuleH.Exec.directBlock, hr] using h
      subst t
      simp [DivisorGraphRuleH.Exec.beforeB, hr]

theorem DivisorGraphRuleH.OfferRefinements.firstATrace_strictly_before (pool : List (List ℕ)) (s : ℤ) (slot : DivisorGraphRuleH.Slot) (A B : DivisorGraphRuleH.Exec.OfferTrace) (hA : DivisorGraphRuleH.Exec.firstATrace pool s slot = some A) (hB : DivisorGraphRuleH.Exec.firstBTrace pool s slot = some B) : A.poolIndex < B.poolIndex := by
  obtain ⟨pre, I, post, hp, hi, _, _, _⟩ :=
    DivisorGraphRuleH.OfferRefinements.taggedFindSome_spec
      (fun J => DivisorGraphRuleH.Exec.shortBlock J s slot) true 0
      (DivisorGraphRuleH.Exec.beforeB pool s slot) A hA
  have hl : A.poolIndex < (DivisorGraphRuleH.Exec.beforeB pool s slot).length := by
    rw [hp]
    simp only [List.length_append, List.length_cons]
    omega
  have hb := DivisorGraphRuleH.OfferRefinements.firstB_prefix_length pool s slot 0 B hB
  omega

theorem DivisorGraphRuleH.OfferRefinements.beforeB_no_direct (pool : List (List ℕ)) (s : ℤ) (slot : DivisorGraphRuleH.Slot) (I : List ℕ) (hI : I ∈ DivisorGraphRuleH.Exec.beforeB pool s slot) : DivisorGraphRuleH.Exec.selectedRoute I s slot = none := by
  have hp : (DivisorGraphRuleH.Exec.selectedRoute I s slot).isNone = true :=
    List.all_eq_true.mp (List.all_takeWhile
      (l := pool) (p := fun J => (DivisorGraphRuleH.Exec.selectedRoute J s slot).isNone)) I hI
  cases hr : DivisorGraphRuleH.Exec.selectedRoute I s slot with
  | none => rfl
  | some r => simp [hr] at hp

theorem DivisorGraphRuleH.OfferRefinements.firstATrace_recomputed (pool : List (List ℕ)) (s : ℤ) (slot : DivisorGraphRuleH.Slot) (A : DivisorGraphRuleH.Exec.OfferTrace) (hA : DivisorGraphRuleH.Exec.firstATrace pool s slot = some A) : ∃ I ∈ DivisorGraphRuleH.Exec.beforeB pool s slot, ∃ J, DivisorGraphRuleH.Exec.shortenedPath I = some J ∧ A.block.inner = J ∧ DivisorGraphRuleH.Exec.selectedRoute J s slot = some A.block.route := by
  obtain ⟨pre, I, post, hp, _, _, hI, _⟩ :=
    DivisorGraphRuleH.OfferRefinements.taggedFindSome_spec
      (fun J => DivisorGraphRuleH.Exec.shortBlock J s slot) true 0
      (DivisorGraphRuleH.Exec.beforeB pool s slot) A hA
  cases hs : DivisorGraphRuleH.Exec.shortenedPath I with
  | none => simp [DivisorGraphRuleH.Exec.shortBlock, hs] at hI
  | some J =>
    cases hr : DivisorGraphRuleH.Exec.selectedRoute J s slot with
    | none => simp [DivisorGraphRuleH.Exec.shortBlock, hs, DivisorGraphRuleH.Exec.directBlock, hr] at hI
    | some r =>
      have hb : (⟨J, r⟩ : DivisorGraphRuleH.TableBlock) = A.block := by
        simpa [DivisorGraphRuleH.Exec.shortBlock, hs, DivisorGraphRuleH.Exec.directBlock, hr] using hI
      refine ⟨I, ?_, J, hs, ?_, ?_⟩
      · rw [hp]
        simp
      · exact (congrArg DivisorGraphRuleH.TableBlock.inner hb).symm
      · rw [← congrArg DivisorGraphRuleH.TableBlock.route hb]
        exact hr

theorem DivisorGraphRuleH.OfferRefinements.chooseTrace_equal_gain_A (A B : DivisorGraphRuleH.Exec.OfferTrace) (h : DivisorGraphRuleH.Exec.gain A.block.inner A.block.route = DivisorGraphRuleH.Exec.gain B.block.inner B.block.route) : DivisorGraphRuleH.Exec.chooseTrace (some A) (some B) = some A := by
  simp only [DivisorGraphRuleH.Exec.chooseTrace, h, le_refl, ite_true]

theorem DivisorGraphRuleH.OfferRefinements.oddPrimeExec_eq : DivisorGraphRuleH.Exec.oddPrimeExec = DivisorGraphRuleH.oddPrime := by
  funext i
  induction i with
  | zero => exact Nat.nth_prime_zero_eq_two.symm
  | succ i ih =>
    simp only [DivisorGraphRuleH.oddPrime] at ih ⊢
    change Nat.find (Nat.exists_infinite_primes (DivisorGraphRuleH.Exec.oddPrimeExec i + 1)) = _
    let h := Nat.exists_infinite_primes (DivisorGraphRuleH.Exec.oddPrimeExec i + 1)
    have hs := Nat.find_spec h
    apply Nat.le_antisymm
    · apply Nat.find_min' h
      constructor
      · rw [ih]
        exact Nat.succ_le_of_lt (Nat.nth_strictMono Nat.infinite_setOf_prime (Nat.lt_succ_self i))
      · exact Nat.prime_nth_prime (i + 1)
    · by_contra hn
      have ht : Nat.find h < Nat.nth Nat.Prime (i + 1) := Nat.lt_of_not_ge hn
      have hp := Nat.le_nth_of_lt_nth_succ ht hs.2
      have hlo := hs.1
      omega

theorem DivisorGraphRuleH.OfferRefinements.toSlotExec_eq : DivisorGraphRuleH.Exec.toSlotExec = DivisorGraphRuleH.Shape.toSlot := by
  funext sh
  unfold DivisorGraphRuleH.Exec.toSlotExec DivisorGraphRuleH.Shape.toSlot
  rw [DivisorGraphRuleH.OfferRefinements.oddPrimeExec_eq]
  all_goals rfl

theorem DivisorGraphRuleH.OfferRefinements.shapeSizeExec_eq : DivisorGraphRuleH.Exec.shapeSizeExec = (fun sh : DivisorGraphRuleH.Shape => sh.toSlot.size) := by
  funext sh
  rw [← DivisorGraphRuleH.OfferRefinements.toSlotExec_eq]
  rcases sh with ⟨kind, index, d⟩
  cases kind <;> rfl

theorem DivisorGraphRuleH.OfferRefinements.shapeKeyExec_eq : DivisorGraphRuleH.Exec.shapeKeyExec = DivisorGraphRuleH.Shape.key := by
  funext sh
  unfold DivisorGraphRuleH.Exec.shapeKeyExec DivisorGraphRuleH.Shape.key
  rw [DivisorGraphRuleH.OfferRefinements.shapeSizeExec_eq]

theorem DivisorGraphRuleH.OfferRefinements.shapeOfRow_kind (d index : ℕ) (kind : DivisorGraphRuleH.SlotKind) : DivisorGraphRuleH.Exec.shapeOfRow d kind.code index = some (⟨kind, index, d⟩ : DivisorGraphRuleH.Shape) := by
  cases kind <;> rfl

theorem DivisorGraphRuleH.OfferRefinements.rowKeyExec_eq (d typeCode index : ℕ) : DivisorGraphRuleH.Exec.rowKeyExec d typeCode index = (DivisorGraphRuleH.Exec.shapeOfRow d typeCode index).map DivisorGraphRuleH.Shape.key := by
  unfold DivisorGraphRuleH.Exec.rowKeyExec
  rw [DivisorGraphRuleH.OfferRefinements.shapeKeyExec_eq]

theorem DivisorGraphRuleH.OfferRefinements.observeOffer_eq (pool : List (List ℕ)) (s : ℤ) (slot : DivisorGraphRuleH.Slot) : DivisorGraphRuleH.Exec.observeOffer pool s slot = (DivisorGraphRuleH.Exec.offerTrace pool s slot).map (fun t => (⟨t.block.inner.length, DivisorGraphRuleH.linkCount t.block.route, t.shortened, DivisorGraphRuleH.gain t.block.inner t.block.route⟩ : DivisorGraphRuleH.Exec.OfferObservation)) := by
  unfold DivisorGraphRuleH.Exec.observeOffer DivisorGraphRuleH.Exec.observeTrace
  rw [DivisorGraphRuleH.SequenceRefinements.linkCount_eq, DivisorGraphRuleH.SequenceRefinements.gain_eq]

theorem DivisorGraphRuleH.OfferRefinements.oddPrimeFast_eq : DivisorGraphRuleH.Exec.oddPrimeFast = DivisorGraphRuleH.oddPrime := by
  funext i
  induction i with
  | zero => exact Nat.nth_prime_zero_eq_two.symm
  | succ i ih =>
    simp only [DivisorGraphRuleH.oddPrime] at ih ⊢
    change Nat.find (Nat.exists_infinite_primes (DivisorGraphRuleH.Exec.oddPrimeFast i + 1)) = _
    let h := Nat.exists_infinite_primes (DivisorGraphRuleH.Exec.oddPrimeFast i + 1)
    have hs := Nat.find_spec h
    apply Nat.le_antisymm
    · apply Nat.find_min' h
      constructor
      · rw [ih]
        exact Nat.succ_le_of_lt (Nat.nth_strictMono Nat.infinite_setOf_prime (Nat.lt_succ_self i))
      · exact Nat.prime_nth_prime (i + 1)
    · by_contra hn
      have ht : Nat.find h < Nat.nth Nat.Prime (i + 1) := Nat.lt_of_not_ge hn
      have hp := Nat.le_nth_of_lt_nth_succ ht hs.2
      have hlo := hs.1
      omega

theorem DivisorGraphRuleH.OfferRefinements.toSlotFast_eq : DivisorGraphRuleH.Exec.toSlotFast = DivisorGraphRuleH.Shape.toSlot := by
  funext sh
  unfold DivisorGraphRuleH.Exec.toSlotFast DivisorGraphRuleH.Shape.toSlot
  rw [DivisorGraphRuleH.OfferRefinements.oddPrimeFast_eq]
  all_goals rfl

theorem DivisorGraphRuleH.OfferRefinements.shapeSizeFast_eq : DivisorGraphRuleH.Exec.shapeSizeFast = (fun sh : DivisorGraphRuleH.Shape => sh.toSlot.size) := by
  funext sh
  rw [← DivisorGraphRuleH.OfferRefinements.toSlotFast_eq]
  rcases sh with ⟨kind, index, d⟩
  cases kind <;> rfl

theorem DivisorGraphRuleH.OfferRefinements.shapeKeyFast_eq : DivisorGraphRuleH.Exec.shapeKeyFast = DivisorGraphRuleH.Shape.key := by
  funext sh
  unfold DivisorGraphRuleH.Exec.shapeKeyFast DivisorGraphRuleH.Shape.key
  rw [DivisorGraphRuleH.OfferRefinements.shapeSizeFast_eq]

theorem DivisorGraphRuleH.OfferRefinements.rowKeyFast_eq (d typeCode index : ℕ) : DivisorGraphRuleH.Exec.rowKeyFast d typeCode index = (DivisorGraphRuleH.Exec.shapeOfRow d typeCode index).map DivisorGraphRuleH.Shape.key := by
  unfold DivisorGraphRuleH.Exec.rowKeyFast
  rw [DivisorGraphRuleH.OfferRefinements.shapeKeyFast_eq]

theorem DivisorGraphRuleH.OfferRefinements.primesUpTo_mem (bound p : ℕ) : p ∈ DivisorGraphRuleH.Exec.primesUpTo bound ↔ p ≤ bound ∧ Nat.Prime p := by
  simp only [DivisorGraphRuleH.Exec.primesUpTo, List.mem_filter, List.mem_range,
    decide_eq_true_eq, Nat.lt_succ_iff]

theorem DivisorGraphRuleH.OfferRefinements.oddPrimeFast_one : DivisorGraphRuleH.Exec.oddPrimeFast 1 = 3 := by
  rw [DivisorGraphRuleH.OfferRefinements.oddPrimeFast_eq]
  exact Nat.nth_prime_one_eq_three

def DivisorGraphRuleH.OfferRefinements.results : Unit := ()
