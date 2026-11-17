import RuleHRelease.Theorems.OfferedInsertion


section
set_option autoImplicit false


theorem RuleHRelease.C_offer :
    ∀ (N p j : ℕ) (hN : 0 < N) (hp : 0 < p)
    (s : ℤ) (hs : s = ((j / p : ℕ) : ℤ))
    (pool : List (List ℕ))
    (hpool : ∀ J ∈ pool, DivisorGraphRuleH.TablePathAt J s)
    (slot : DivisorGraphRuleH.Slot) (hslot : slot.Valid)
    (hsize : (slot.size : ℤ) ≤ s)
    (block : DivisorGraphRuleH.TableBlock)
    (hoffer : DivisorGraphRuleH.offer pool s slot = some block), DivisorGraphRuleH.TablePathAt block.inner s ∧
    DivisorGraphRuleH.SearchReturns block.inner s slot block.route ∧
    (DivisorGraphRuleH.framedBlock slot N p block).IsChain
        DivisorGraphRuleH.Comparable ∧
    (DivisorGraphRuleH.scaledCofactors N p block).Nodup ∧
    (∀ t ∈ DivisorGraphRuleH.scaledCofactors N p block,
      p * N ∣ t ∧ t ≤ N * j) ∧
    (DivisorGraphRuleH.scaledCofactors N p block).length =
        block.inner.length + DivisorGraphRuleH.linkCount block.route ∧
    block.inner.length + DivisorGraphRuleH.linkCount block.route =
      1 + DivisorGraphRuleH.gain block.inner block.route :=
  @DivisorGraphRuleH.C_offer
end
