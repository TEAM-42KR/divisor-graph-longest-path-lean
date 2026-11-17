import RuleHRelease.Heads
import RuleHRelease.Definitions.Foundation
import RuleHRelease.Definitions.Arithmetic
import RuleHRelease.Definitions.IndexWords
import RuleHRelease.Definitions.Shortening
import RuleHRelease.Definitions.ForwardRoutes
import RuleHRelease.Definitions.RoutePaths
import RuleHRelease.Definitions.OrderedSearch
import RuleHRelease.Definitions.CofactorPaths
import RuleHRelease.Definitions.Feasibility
import RuleHRelease.Definitions.RouteExistence
import RuleHRelease.Definitions.Offers
import RuleHRelease.Definitions.Directories
import RuleHRelease.Definitions.LocalInsertion
import RuleHRelease.Definitions.SequenceRefinements
import RuleHRelease.Definitions.OfferRefinements

set_option autoImplicit false

namespace DivisorGraphRuleH.PublicStatements
noncomputable section
attribute [local instance] Classical.propDecidable

theorem R0 (J : List ℕ) (hJ : TablePath J) (hn : 2 ≤ lastIndex J) :
    e J (lastIndex J - 1) ∧ 4 ≤ term J (lastIndex J - 1) := by
  exact @DivisorGraphRuleH.R0 J hJ hn

theorem H1 (J : List ℕ) (s : ℤ) (hJ : TablePathAt J s)
    (u w : ℕ) (hu : u < J.length) (hw : w < J.length)
    (hne : u ≠ w) (hfeasible : Feasible J u w) :
    (routeIndices J u w).Perm (List.range J.length) ∧
    (routeIndices J u w).head? = some u ∧
    (routeIndices J u w).getLast? = some w ∧
    (routeIndices J u w).IsChain (fun i i' => Comparable (term J i) (term J i')) ∧
    DivisorPath (routeOrder J u w) ∧
    (routeOrder J u w).head? = some (term J u) ∧
    (routeOrder J u w).getLast? = some (term J w) ∧
    (routeOrder J u w).Perm J := by
  exact @DivisorGraphRuleH.H1 J s hJ u w hu hw hne hfeasible

theorem H2 (J : List ℕ) (s : ℤ) (hJ : TablePathAt J s)
    (hn : 2 ≤ lastIndex J) (hodd : Odd (term J 1)) :
    ∃ k : ℕ, FirstEven J k ∧ 2 ≤ k ∧ k ≤ lastIndex J - 1 ∧
      shortenedPath J = some (1 :: J.drop k) ∧
      TablePathAt (1 :: J.drop k) s ∧
      3 ≤ (1 :: J.drop k).length ∧
      (∀ c ∈ (1 :: J.drop k), c ∈ J) ∧ e (1 :: J.drop k) 1 := by
  exact @DivisorGraphRuleH.H2 J s hJ hn hodd

theorem H3 (J : List ℕ) (s : ℤ) (hJ : TablePathAt J s)
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
  exact @DivisorGraphRuleH.H3 J s hJ slot hslot hsize r hfound

theorem H4 (J : List ℕ) (s : ℤ) (hJ : TablePathAt J s) (he : e J 1) :
    (∀ u w, u < J.length → w < J.length → u ≠ w → Feasible J u w) ∧
    (∀ slot : Slot, slot.Valid → (slot.size : ℤ) ≤ s →
      ∃ r, SearchReturns J s slot r) := by
  exact @DivisorGraphRuleH.H4 J s hJ he

theorem H5 (pool : List (List ℕ)) (s : ℤ)
    (hnonempty : pool ≠ []) (hpool : ∀ J ∈ pool, TablePathAt J s)
    (slot : Slot) (hslot : slot.Valid) (hsize : (slot.size : ℤ) ≤ s) :
    ∃ block : TableBlock, offer pool s slot = some block := by
  exact @DivisorGraphRuleH.H5 pool s hnonempty hpool slot hslot hsize

theorem H5_directory (D : PoolDirectory) (hD : PoolHypotheses D)
    (s : ℤ) (hs : 6 ≤ s ∧ s ≤ (D.scale : ℤ))
    (slot : Slot) (hslot : slot.Valid) (hsize : (slot.size : ℤ) ≤ s) :
    pathPool D s ≠ [] ∧
    ∃ block : TableBlock, offer (pathPool D s) s slot = some block := by
  exact @DivisorGraphRuleH.H5_directory D hD s hs slot hslot hsize

theorem C_local (N p j : ℕ) (hN : 0 < N) (hp : 0 < p)
    (s : ℤ) (hs : s = ((j / p : ℕ) : ℤ))
    (J : List ℕ) (hJ : DivisorGraphRuleH.TablePathAt J s)
    (slot : DivisorGraphRuleH.Slot) (hslot : slot.Valid)
    (hsize : (slot.size : ℤ) ≤ s)
    (r : DivisorGraphRuleH.Route)
    (hfound : DivisorGraphRuleH.SearchReturns J s slot r) :
    (DivisorGraphRuleH.framedBlock slot N p
      (⟨J, r⟩ : DivisorGraphRuleH.TableBlock)).IsChain
        DivisorGraphRuleH.Comparable ∧
    (DivisorGraphRuleH.scaledCofactors N p
      (⟨J, r⟩ : DivisorGraphRuleH.TableBlock)).Nodup ∧
    (∀ t ∈ DivisorGraphRuleH.scaledCofactors N p
        (⟨J, r⟩ : DivisorGraphRuleH.TableBlock),
      p * N ∣ t ∧ t ≤ N * j) ∧
    (DivisorGraphRuleH.scaledCofactors N p
      (⟨J, r⟩ : DivisorGraphRuleH.TableBlock)).length =
        J.length + DivisorGraphRuleH.linkCount r ∧
    J.length + DivisorGraphRuleH.linkCount r =
      1 + DivisorGraphRuleH.gain J r := by
  exact @DivisorGraphRuleH.C_local N p j hN hp s hs J hJ slot hslot hsize r hfound

theorem C_offer (N p j : ℕ) (hN : 0 < N) (hp : 0 < p)
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
  exact @DivisorGraphRuleH.C_offer N p j hN hp s hs pool hpool slot hslot hsize block hoffer

end
end DivisorGraphRuleH.PublicStatements

#print axioms DivisorGraphRuleH.PublicStatements.R0
#print axioms DivisorGraphRuleH.PublicStatements.H1
#print axioms DivisorGraphRuleH.PublicStatements.H2
#print axioms DivisorGraphRuleH.PublicStatements.H3
#print axioms DivisorGraphRuleH.PublicStatements.H4
#print axioms DivisorGraphRuleH.PublicStatements.H5
#print axioms DivisorGraphRuleH.PublicStatements.H5_directory
#print axioms DivisorGraphRuleH.PublicStatements.C_local
#print axioms DivisorGraphRuleH.PublicStatements.C_offer
