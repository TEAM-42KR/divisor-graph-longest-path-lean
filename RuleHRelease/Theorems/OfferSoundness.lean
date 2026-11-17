import RuleHRelease.Proofs.OfferSoundness
import Mathlib
import RuleHRelease.Definitions.LocalInsertion
import RuleHRelease.Definitions.Offers
set_option autoImplicit false


theorem DivisorGraphRuleH.OfferSoundness.offer_sound :
    ∀ (pool : List (List ℕ)) (s : ℤ)
    (hpool : ∀ J ∈ pool, DivisorGraphRuleH.TablePathAt J s)
    (slot : DivisorGraphRuleH.Slot) (block : DivisorGraphRuleH.TableBlock)
    (hoffer : DivisorGraphRuleH.offer pool s slot = some block), DivisorGraphRuleH.TablePathAt block.inner s ∧
    DivisorGraphRuleH.SearchReturns block.inner s slot block.route :=
  @proofOfferSoundness
