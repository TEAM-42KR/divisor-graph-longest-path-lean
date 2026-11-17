import Mathlib
import RuleHRelease.Definitions.LocalInsertion
import RuleHRelease.Definitions.Offers
set_option autoImplicit false

theorem proofOfferSoundness (pool : List (List ℕ)) (s : ℤ)
    (hpool : ∀ J ∈ pool, DivisorGraphRuleH.TablePathAt J s)
    (slot : DivisorGraphRuleH.Slot) (block : DivisorGraphRuleH.TableBlock)
    (hoffer : DivisorGraphRuleH.offer pool s slot = some block) :
    DivisorGraphRuleH.TablePathAt block.inner s ∧
    DivisorGraphRuleH.SearchReturns block.inner s slot block.route := by
  have hdirect : ∀ (J : List ℕ), DivisorGraphRuleH.TablePathAt J s →
      ∀ (b : DivisorGraphRuleH.TableBlock),
        DivisorGraphRuleH.directBlock J s slot = some b →
        DivisorGraphRuleH.TablePathAt b.inner s ∧
          DivisorGraphRuleH.SearchReturns b.inner s slot b.route := by
    intro J hJ b hb
    cases hr : DivisorGraphRuleH.selectedRoute J s slot with
    | none =>
      simp only [DivisorGraphRuleH.directBlock, hr, Option.map_none] at hb
      cases hb
    | some r =>
      have heq : (⟨J, r⟩ : DivisorGraphRuleH.TableBlock) = b :=
        Option.some.inj (by simpa only [DivisorGraphRuleH.directBlock, hr, Option.map_some] using hb)
      subst b
      exact ⟨hJ, hr⟩
  have hshort : ∀ (I : List ℕ), DivisorGraphRuleH.TablePathAt I s →
      ∀ (b : DivisorGraphRuleH.TableBlock),
        DivisorGraphRuleH.shortBlock I s slot = some b →
        DivisorGraphRuleH.TablePathAt b.inner s ∧
          DivisorGraphRuleH.SearchReturns b.inner s slot b.route := by
    intro I hI b hb
    cases hs : DivisorGraphRuleH.shortenedPath I with
    | none =>
      simp only [DivisorGraphRuleH.shortBlock, hs, Option.bind_none] at hb
      cases hb
    | some J =>
      have hguard : 2 ≤ DivisorGraphRuleH.lastIndex I ∧ ¬ DivisorGraphRuleH.e I 1 := by
        by_cases hg : 2 ≤ DivisorGraphRuleH.lastIndex I ∧ ¬ DivisorGraphRuleH.e I 1
        · exact hg
        · simp only [DivisorGraphRuleH.shortenedPath, if_neg hg] at hs
          cases hs
      obtain ⟨k, _, _, _, hk, hK, _, _, _⟩ :=
        DivisorGraphRuleH.H2 I s hI hguard.1 (Nat.not_even_iff_odd.mp hguard.2)
      have heq : 1 :: I.drop k = J := Option.some.inj (hk.symm.trans hs)
      have hJ : DivisorGraphRuleH.TablePathAt J s := heq ▸ hK
      exact hdirect J hJ b (by simpa only [DivisorGraphRuleH.shortBlock, hs, Option.bind_some] using hb)
  have hfirstA : ∀ b : DivisorGraphRuleH.TableBlock,
      DivisorGraphRuleH.firstA pool s slot = some b →
      DivisorGraphRuleH.TablePathAt b.inner s ∧
        DivisorGraphRuleH.SearchReturns b.inner s slot b.route := by
    intro b hb
    obtain ⟨I, hI, hIb⟩ := List.exists_of_findSome?_eq_some hb
    have hmem : I ∈ pool := (List.takeWhile_prefix _).subset hI
    exact hshort I (hpool I hmem) b hIb
  have hfirstB : ∀ b : DivisorGraphRuleH.TableBlock,
      DivisorGraphRuleH.firstB pool s slot = some b →
      DivisorGraphRuleH.TablePathAt b.inner s ∧
        DivisorGraphRuleH.SearchReturns b.inner s slot b.route := by
    intro b hb
    obtain ⟨J, hJ, hJb⟩ := List.exists_of_findSome?_eq_some hb
    exact hdirect J (hpool J hJ) b hJb
  cases hA : DivisorGraphRuleH.firstA pool s slot with
  | none =>
    cases hB : DivisorGraphRuleH.firstB pool s slot with
    | none =>
      simp only [DivisorGraphRuleH.offer, hA, hB] at hoffer
      cases hoffer
    | some B =>
      have heq : B = block :=
        Option.some.inj (by simpa only [DivisorGraphRuleH.offer, hA, hB] using hoffer)
      subst block
      exact hfirstB B hB
  | some A =>
    cases hB : DivisorGraphRuleH.firstB pool s slot with
    | none =>
      have heq : A = block :=
        Option.some.inj (by simpa only [DivisorGraphRuleH.offer, hA, hB] using hoffer)
      subst block
      exact hfirstA A hA
    | some B =>
      by_cases hg : DivisorGraphRuleH.gain A.inner A.route ≥ DivisorGraphRuleH.gain B.inner B.route
      · have heq : A = block :=
          Option.some.inj (by simpa only [DivisorGraphRuleH.offer, hA, hB, if_pos hg] using hoffer)
        subst block
        exact hfirstA A hA
      · have heq : B = block :=
          Option.some.inj (by simpa only [DivisorGraphRuleH.offer, hA, hB, if_neg hg] using hoffer)
        subst block
        exact hfirstB B hB
