import Mathlib
import RuleHRelease.Definitions.LocalInsertion
import RuleHRelease.Definitions.Offers
import RuleHRelease.Theorems.OfferSoundness
set_option autoImplicit false

theorem proofOfferedInsertion (N p j : ℕ) (hN : 0 < N) (hp : 0 < p)
    (s : ℤ) (hs : s = ((j / p : ℕ) : ℤ))
    (pool : List (List ℕ))
    (hpool : ∀ J ∈ pool, DivisorGraphRuleH.TablePathAt J s)
    (slot : DivisorGraphRuleH.Slot) (hslot : slot.Valid)
    (hsize : (slot.size : ℤ) ≤ s)
    (block : DivisorGraphRuleH.TableBlock)
    (hoffer : DivisorGraphRuleH.offer pool s slot = some block) :
    DivisorGraphRuleH.TablePathAt block.inner s ∧
    DivisorGraphRuleH.SearchReturns block.inner s slot block.route ∧
    (DivisorGraphRuleH.framedBlock slot N p block).IsChain
        DivisorGraphRuleH.Comparable ∧
    (DivisorGraphRuleH.scaledCofactors N p block).Nodup ∧
    (∀ t ∈ DivisorGraphRuleH.scaledCofactors N p block,
      p * N ∣ t ∧ t ≤ N * j) ∧
    (DivisorGraphRuleH.scaledCofactors N p block).length =
        block.inner.length + DivisorGraphRuleH.linkCount block.route ∧
    block.inner.length + DivisorGraphRuleH.linkCount block.route =
      1 + DivisorGraphRuleH.gain block.inner block.route := by
  obtain ⟨hinner, hsearch⟩ :=
    DivisorGraphRuleH.OfferSoundness.offer_sound pool s hpool slot block hoffer
  exact ⟨hinner, hsearch,
    DivisorGraphRuleH.C_local N p j hN hp s hs block.inner hinner
      slot hslot hsize block.route hsearch⟩
