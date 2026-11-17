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
import ExactStatements
import Lean

set_option autoImplicit false

example : DivisorGraphRuleH.Exec.lastIndex = DivisorGraphRuleH.lastIndex := @DivisorGraphRuleH.SequenceRefinements.lastIndex_eq

example : DivisorGraphRuleH.Exec.term = DivisorGraphRuleH.term := @DivisorGraphRuleH.SequenceRefinements.term_eq

example : DivisorGraphRuleH.Exec.e = DivisorGraphRuleH.e := @DivisorGraphRuleH.SequenceRefinements.e_eq

example : DivisorGraphRuleH.Exec.parity = (fun (J : List ℕ) (k : ℕ) => @decide (DivisorGraphRuleH.e J k) (Classical.propDecidable _)) := @DivisorGraphRuleH.SequenceRefinements.parity_eq

example : DivisorGraphRuleH.Exec.up = DivisorGraphRuleH.up := @DivisorGraphRuleH.SequenceRefinements.up_eq

example : DivisorGraphRuleH.Exec.down = DivisorGraphRuleH.down := @DivisorGraphRuleH.SequenceRefinements.down_eq

example : DivisorGraphRuleH.Exec.freeMultiples = DivisorGraphRuleH.freeMultiples := @DivisorGraphRuleH.SequenceRefinements.freeMultiples_eq

example : DivisorGraphRuleH.Exec.interiorIndices = DivisorGraphRuleH.interiorIndices := @DivisorGraphRuleH.SequenceRefinements.interiorIndices_eq

example : DivisorGraphRuleH.Exec.forwardH = DivisorGraphRuleH.forwardH := @DivisorGraphRuleH.SequenceRefinements.forwardH_eq

example : DivisorGraphRuleH.Exec.H = DivisorGraphRuleH.H := @DivisorGraphRuleH.SequenceRefinements.H_eq

example : DivisorGraphRuleH.Exec.Feasible = DivisorGraphRuleH.Feasible := @DivisorGraphRuleH.SequenceRefinements.Feasible_eq

example : DivisorGraphRuleH.Exec.routeIndices = DivisorGraphRuleH.routeIndices := @DivisorGraphRuleH.SequenceRefinements.routeIndices_eq

example : DivisorGraphRuleH.Exec.routeOrder = DivisorGraphRuleH.routeOrder := @DivisorGraphRuleH.SequenceRefinements.routeOrder_eq

example : DivisorGraphRuleH.Exec.A1 = DivisorGraphRuleH.A1 := @DivisorGraphRuleH.SequenceRefinements.A1_eq

example : DivisorGraphRuleH.Exec.A2 = DivisorGraphRuleH.A2 := @DivisorGraphRuleH.SequenceRefinements.A2_eq

example : DivisorGraphRuleH.Exec.A3 = DivisorGraphRuleH.A3 := @DivisorGraphRuleH.SequenceRefinements.A3_eq

example : DivisorGraphRuleH.Exec.B1 = DivisorGraphRuleH.B1 := @DivisorGraphRuleH.SequenceRefinements.B1_eq

example : DivisorGraphRuleH.Exec.B2 = DivisorGraphRuleH.B2 := @DivisorGraphRuleH.SequenceRefinements.B2_eq

example : DivisorGraphRuleH.Exec.B3 = DivisorGraphRuleH.B3 := @DivisorGraphRuleH.SequenceRefinements.B3_eq

example : DivisorGraphRuleH.Exec.startOptions = DivisorGraphRuleH.startOptions := @DivisorGraphRuleH.SequenceRefinements.startOptions_eq

example : DivisorGraphRuleH.Exec.endOptions = DivisorGraphRuleH.endOptions := @DivisorGraphRuleH.SequenceRefinements.endOptions_eq

example : DivisorGraphRuleH.Exec.R1 = DivisorGraphRuleH.R1 := @DivisorGraphRuleH.SequenceRefinements.R1_eq

example : DivisorGraphRuleH.Exec.R2 = DivisorGraphRuleH.R2 := @DivisorGraphRuleH.SequenceRefinements.R2_eq

example : DivisorGraphRuleH.Exec.R3 = DivisorGraphRuleH.R3 := @DivisorGraphRuleH.SequenceRefinements.R3_eq

example : DivisorGraphRuleH.Exec.R4 = DivisorGraphRuleH.R4 := @DivisorGraphRuleH.SequenceRefinements.R4_eq

example : DivisorGraphRuleH.Exec.noLinkStarts = DivisorGraphRuleH.noLinkStarts := @DivisorGraphRuleH.SequenceRefinements.noLinkStarts_eq

example : DivisorGraphRuleH.Exec.noLinkEnds = DivisorGraphRuleH.noLinkEnds := @DivisorGraphRuleH.SequenceRefinements.noLinkEnds_eq

example : DivisorGraphRuleH.Exec.R5 = DivisorGraphRuleH.R5 := @DivisorGraphRuleH.SequenceRefinements.R5_eq

example : DivisorGraphRuleH.Exec.routesOfKind = DivisorGraphRuleH.routesOfKind := @DivisorGraphRuleH.SequenceRefinements.routesOfKind_eq

example : DivisorGraphRuleH.Exec.rankedRoutes = DivisorGraphRuleH.rankedRoutes := @DivisorGraphRuleH.SequenceRefinements.rankedRoutes_eq

example : DivisorGraphRuleH.Exec.selectedRoute = DivisorGraphRuleH.selectedRoute := @DivisorGraphRuleH.SequenceRefinements.selectedRoute_eq

example : DivisorGraphRuleH.Exec.cofactors = DivisorGraphRuleH.cofactors := @DivisorGraphRuleH.SequenceRefinements.cofactors_eq

example : DivisorGraphRuleH.Exec.linkCount = DivisorGraphRuleH.linkCount := @DivisorGraphRuleH.SequenceRefinements.linkCount_eq

example : DivisorGraphRuleH.Exec.gain = DivisorGraphRuleH.gain := @DivisorGraphRuleH.SequenceRefinements.gain_eq

example : DivisorGraphRuleH.Exec.firstEvenIndex = DivisorGraphRuleH.firstEvenIndex := @DivisorGraphRuleH.SequenceRefinements.firstEvenIndex_eq

example : DivisorGraphRuleH.Exec.shortenedPath = DivisorGraphRuleH.shortenedPath := @DivisorGraphRuleH.SequenceRefinements.shortenedPath_eq

example : DivisorGraphRuleH.Exec.feasible = (fun (J : List ℕ) (u w : ℕ) => @decide (DivisorGraphRuleH.Feasible J u w) (Classical.propDecidable _)) := @DivisorGraphRuleH.SequenceRefinements.feasible_eq

example : DivisorGraphRuleH.Exec.directBlock = DivisorGraphRuleH.directBlock := @DivisorGraphRuleH.OfferRefinements.directBlock_eq

example : DivisorGraphRuleH.Exec.shortBlock = DivisorGraphRuleH.shortBlock := @DivisorGraphRuleH.OfferRefinements.shortBlock_eq

example : DivisorGraphRuleH.Exec.firstB = DivisorGraphRuleH.firstB := @DivisorGraphRuleH.OfferRefinements.firstB_eq

example : DivisorGraphRuleH.Exec.beforeB = DivisorGraphRuleH.beforeB := @DivisorGraphRuleH.OfferRefinements.beforeB_eq

example : DivisorGraphRuleH.Exec.firstA = DivisorGraphRuleH.firstA := @DivisorGraphRuleH.OfferRefinements.firstA_eq

example : DivisorGraphRuleH.Exec.offerExec = DivisorGraphRuleH.offer := @DivisorGraphRuleH.OfferRefinements.offerExec_eq

example : ∀ (f : List ℕ → Option DivisorGraphRuleH.TableBlock) (flag : Bool) (offset : ℕ) (pool : List (List ℕ)), (DivisorGraphRuleH.Exec.taggedFindSome f flag offset pool).map DivisorGraphRuleH.Exec.OfferTrace.block = pool.findSome? f := @DivisorGraphRuleH.OfferRefinements.taggedFindSome_project

example : ∀ (pool : List (List ℕ)) (s : ℤ) (slot : DivisorGraphRuleH.Slot), (DivisorGraphRuleH.Exec.firstBTrace pool s slot).map DivisorGraphRuleH.Exec.OfferTrace.block = DivisorGraphRuleH.firstB pool s slot := @DivisorGraphRuleH.OfferRefinements.firstBTrace_project

example : ∀ (pool : List (List ℕ)) (s : ℤ) (slot : DivisorGraphRuleH.Slot), (DivisorGraphRuleH.Exec.firstATrace pool s slot).map DivisorGraphRuleH.Exec.OfferTrace.block = DivisorGraphRuleH.firstA pool s slot := @DivisorGraphRuleH.OfferRefinements.firstATrace_project

example : ∀ (A B : Option DivisorGraphRuleH.Exec.OfferTrace), (DivisorGraphRuleH.Exec.chooseTrace A B).map DivisorGraphRuleH.Exec.OfferTrace.block = DivisorGraphRuleH.Exec.chooseBlock (A.map DivisorGraphRuleH.Exec.OfferTrace.block) (B.map DivisorGraphRuleH.Exec.OfferTrace.block) := @DivisorGraphRuleH.OfferRefinements.chooseTrace_project

example : ∀ (pool : List (List ℕ)) (s : ℤ) (slot : DivisorGraphRuleH.Slot), (DivisorGraphRuleH.Exec.offerTrace pool s slot).map DivisorGraphRuleH.Exec.OfferTrace.block = DivisorGraphRuleH.offer pool s slot := @DivisorGraphRuleH.OfferRefinements.offerTrace_project

example : ∀ (f : List ℕ → Option DivisorGraphRuleH.TableBlock) (flag : Bool) (offset : ℕ) (pool : List (List ℕ)) (t : DivisorGraphRuleH.Exec.OfferTrace) (h : DivisorGraphRuleH.Exec.taggedFindSome f flag offset pool = some t), ∃ pre I post, pool = pre ++ I :: post ∧ t.poolIndex = offset + pre.length ∧ t.shortened = flag ∧ f I = some t.block ∧ ∀ J ∈ pre, f J = none := @DivisorGraphRuleH.OfferRefinements.taggedFindSome_spec

example : ∀ (pool : List (List ℕ)) (s : ℤ) (slot : DivisorGraphRuleH.Slot) (offset : ℕ) (t : DivisorGraphRuleH.Exec.OfferTrace) (h : DivisorGraphRuleH.Exec.taggedFindSome (fun J => DivisorGraphRuleH.Exec.directBlock J s slot) false offset pool = some t), (DivisorGraphRuleH.Exec.beforeB pool s slot).length + offset = t.poolIndex := @DivisorGraphRuleH.OfferRefinements.firstB_prefix_length

example : ∀ (pool : List (List ℕ)) (s : ℤ) (slot : DivisorGraphRuleH.Slot) (A B : DivisorGraphRuleH.Exec.OfferTrace) (hA : DivisorGraphRuleH.Exec.firstATrace pool s slot = some A) (hB : DivisorGraphRuleH.Exec.firstBTrace pool s slot = some B), A.poolIndex < B.poolIndex := @DivisorGraphRuleH.OfferRefinements.firstATrace_strictly_before

example : ∀ (pool : List (List ℕ)) (s : ℤ) (slot : DivisorGraphRuleH.Slot) (I : List ℕ) (hI : I ∈ DivisorGraphRuleH.Exec.beforeB pool s slot), DivisorGraphRuleH.Exec.selectedRoute I s slot = none := @DivisorGraphRuleH.OfferRefinements.beforeB_no_direct

example : ∀ (pool : List (List ℕ)) (s : ℤ) (slot : DivisorGraphRuleH.Slot) (A : DivisorGraphRuleH.Exec.OfferTrace) (hA : DivisorGraphRuleH.Exec.firstATrace pool s slot = some A), ∃ I ∈ DivisorGraphRuleH.Exec.beforeB pool s slot, ∃ J, DivisorGraphRuleH.Exec.shortenedPath I = some J ∧ A.block.inner = J ∧ DivisorGraphRuleH.Exec.selectedRoute J s slot = some A.block.route := @DivisorGraphRuleH.OfferRefinements.firstATrace_recomputed

example : ∀ (A B : DivisorGraphRuleH.Exec.OfferTrace) (h : DivisorGraphRuleH.Exec.gain A.block.inner A.block.route = DivisorGraphRuleH.Exec.gain B.block.inner B.block.route), DivisorGraphRuleH.Exec.chooseTrace (some A) (some B) = some A := @DivisorGraphRuleH.OfferRefinements.chooseTrace_equal_gain_A

example : DivisorGraphRuleH.Exec.oddPrimeExec = DivisorGraphRuleH.oddPrime := @DivisorGraphRuleH.OfferRefinements.oddPrimeExec_eq

example : DivisorGraphRuleH.Exec.toSlotExec = DivisorGraphRuleH.Shape.toSlot := @DivisorGraphRuleH.OfferRefinements.toSlotExec_eq

example : DivisorGraphRuleH.Exec.shapeSizeExec = (fun sh : DivisorGraphRuleH.Shape => sh.toSlot.size) := @DivisorGraphRuleH.OfferRefinements.shapeSizeExec_eq

example : DivisorGraphRuleH.Exec.shapeKeyExec = DivisorGraphRuleH.Shape.key := @DivisorGraphRuleH.OfferRefinements.shapeKeyExec_eq

example : ∀ (d index : ℕ) (kind : DivisorGraphRuleH.SlotKind), DivisorGraphRuleH.Exec.shapeOfRow d kind.code index = some (⟨kind, index, d⟩ : DivisorGraphRuleH.Shape) := @DivisorGraphRuleH.OfferRefinements.shapeOfRow_kind

example : ∀ (d typeCode index : ℕ), DivisorGraphRuleH.Exec.rowKeyExec d typeCode index = (DivisorGraphRuleH.Exec.shapeOfRow d typeCode index).map DivisorGraphRuleH.Shape.key := @DivisorGraphRuleH.OfferRefinements.rowKeyExec_eq

example : ∀ (pool : List (List ℕ)) (s : ℤ) (slot : DivisorGraphRuleH.Slot), DivisorGraphRuleH.Exec.observeOffer pool s slot = (DivisorGraphRuleH.Exec.offerTrace pool s slot).map (fun t => (⟨t.block.inner.length, DivisorGraphRuleH.linkCount t.block.route, t.shortened, DivisorGraphRuleH.gain t.block.inner t.block.route⟩ : DivisorGraphRuleH.Exec.OfferObservation)) := @DivisorGraphRuleH.OfferRefinements.observeOffer_eq

example : DivisorGraphRuleH.Exec.oddPrimeFast = DivisorGraphRuleH.oddPrime := @DivisorGraphRuleH.OfferRefinements.oddPrimeFast_eq

example : DivisorGraphRuleH.Exec.toSlotFast = DivisorGraphRuleH.Shape.toSlot := @DivisorGraphRuleH.OfferRefinements.toSlotFast_eq

example : DivisorGraphRuleH.Exec.shapeSizeFast = (fun sh : DivisorGraphRuleH.Shape => sh.toSlot.size) := @DivisorGraphRuleH.OfferRefinements.shapeSizeFast_eq

example : DivisorGraphRuleH.Exec.shapeKeyFast = DivisorGraphRuleH.Shape.key := @DivisorGraphRuleH.OfferRefinements.shapeKeyFast_eq

example : ∀ (d typeCode index : ℕ), DivisorGraphRuleH.Exec.rowKeyFast d typeCode index = (DivisorGraphRuleH.Exec.shapeOfRow d typeCode index).map DivisorGraphRuleH.Shape.key := @DivisorGraphRuleH.OfferRefinements.rowKeyFast_eq

example : ∀ (bound p : ℕ), p ∈ DivisorGraphRuleH.Exec.primesUpTo bound ↔ p ≤ bound ∧ Nat.Prime p := @DivisorGraphRuleH.OfferRefinements.primesUpTo_mem

example : DivisorGraphRuleH.Exec.oddPrimeFast 1 = 3 := @DivisorGraphRuleH.OfferRefinements.oddPrimeFast_one

open Lean Elab Command

run_cmd do
  let permitted : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let results : List Name := [
    ``DivisorGraphRuleH.Foundation.down_endpoints,
    ``DivisorGraphRuleH.Foundation.down_eq_nil,
    ``DivisorGraphRuleH.Foundation.down_getElem,
    ``DivisorGraphRuleH.Foundation.down_length,
    ``DivisorGraphRuleH.Foundation.down_nodup,
    ``DivisorGraphRuleH.Foundation.lastIndex_bounds,
    ``DivisorGraphRuleH.Foundation.mem_down,
    ``DivisorGraphRuleH.Foundation.mem_up,
    ``DivisorGraphRuleH.Foundation.tablePathAt_two_le,
    ``DivisorGraphRuleH.Foundation.tablePath_endpoints_mem,
    ``DivisorGraphRuleH.Foundation.tablePath_length,
    ``DivisorGraphRuleH.Foundation.tablePath_parts,
    ``DivisorGraphRuleH.Foundation.term_adjacent,
    ``DivisorGraphRuleH.Foundation.term_first,
    ``DivisorGraphRuleH.Foundation.term_getElem,
    ``DivisorGraphRuleH.Foundation.term_index_of_mem,
    ``DivisorGraphRuleH.Foundation.term_injective,
    ``DivisorGraphRuleH.Foundation.term_last,
    ``DivisorGraphRuleH.Foundation.term_le_range,
    ``DivisorGraphRuleH.Foundation.term_map_range,
    ``DivisorGraphRuleH.Foundation.term_mem,
    ``DivisorGraphRuleH.Foundation.term_pos,
    ``DivisorGraphRuleH.Foundation.up_endpoints,
    ``DivisorGraphRuleH.Foundation.up_eq_nil,
    ``DivisorGraphRuleH.Foundation.up_getElem,
    ``DivisorGraphRuleH.Foundation.up_length,
    ``DivisorGraphRuleH.Foundation.up_nodup,
    ``DivisorGraphRuleH.Arithmetic.a_dvd_two_iff,
    ``DivisorGraphRuleH.Arithmetic.a_eq_one_iff,
    ``DivisorGraphRuleH.Arithmetic.a_eq_one_moduli,
    ``DivisorGraphRuleH.Arithmetic.a_le_size,
    ``DivisorGraphRuleH.Arithmetic.a_ne_aprime,
    ``DivisorGraphRuleH.Arithmetic.a_ne_two,
    ``DivisorGraphRuleH.Arithmetic.a_pos,
    ``DivisorGraphRuleH.Arithmetic.aprime_dvd_two_iff,
    ``DivisorGraphRuleH.Arithmetic.aprime_le_size,
    ``DivisorGraphRuleH.Arithmetic.aprime_pos,
    ``DivisorGraphRuleH.Arithmetic.consecutiveOddPrimes_lt_two_mul,
    ``DivisorGraphRuleH.Arithmetic.even_a_aprime_lt,
    ``DivisorGraphRuleH.Arithmetic.even_a_lcm,
    ``DivisorGraphRuleH.Arithmetic.even_a_link_ne_aprime,
    ``DivisorGraphRuleH.Arithmetic.even_a_not_dvd_aprime,
    ``DivisorGraphRuleH.Arithmetic.odd_a_double_interior_bounds,
    ``DivisorGraphRuleH.Arithmetic.odd_a_moduli,
    ``DivisorGraphRuleH.Arithmetic.odd_a_type1,
    ``DivisorGraphRuleH.Arithmetic.slot_arithmetic,
    ``DivisorGraphRuleH.Arithmetic.three_le_a_of_ne_one,
    ``DivisorGraphRuleH.Arithmetic.two_le_aprime,
    ``DivisorGraphRuleH.Arithmetic.type2_aprime_lt_a,
    ``DivisorGraphRuleH.Arithmetic.type3_a_eq_two_aprime,
    ``DivisorGraphRuleH.Arithmetic.type3_pow_step,
    ``DivisorGraphRuleH.IndexWords.append_blocks_perm,
    ``DivisorGraphRuleH.IndexWords.append_endpoints,
    ``DivisorGraphRuleH.IndexWords.chain_append_endpoints,
    ``DivisorGraphRuleH.IndexWords.comparable_symm,
    ``DivisorGraphRuleH.IndexWords.down_chain,
    ``DivisorGraphRuleH.IndexWords.down_perm_up,
    ``DivisorGraphRuleH.IndexWords.even_junction,
    ``DivisorGraphRuleH.IndexWords.index_step,
    ``DivisorGraphRuleH.IndexWords.interval_disjoint,
    ``DivisorGraphRuleH.IndexWords.interval_perm_iff,
    ``DivisorGraphRuleH.IndexWords.range_perm_iff,
    ``DivisorGraphRuleH.IndexWords.reverse_chain,
    ``DivisorGraphRuleH.IndexWords.three_positive_blocks_perm,
    ``DivisorGraphRuleH.IndexWords.two_positive_blocks_perm,
    ``DivisorGraphRuleH.IndexWords.up_chain,
    ``DivisorGraphRuleH.IndexWords.up_split,
    ``DivisorGraphRuleH.IndexWords.up_zero_range,
    ``DivisorGraphRuleH.IndexWords.zero_junction,
    ``DivisorGraphRuleH.IndexWords.zero_positive_perm,
    ``DivisorGraphRuleH.IndexWords.zero_stitch,
    ``DivisorGraphRuleH.ForwardRoutes.case_a,
    ``DivisorGraphRuleH.ForwardRoutes.case_b,
    ``DivisorGraphRuleH.ForwardRoutes.case_c,
    ``DivisorGraphRuleH.ForwardRoutes.case_d,
    ``DivisorGraphRuleH.ForwardRoutes.case_e,
    ``DivisorGraphRuleH.ForwardRoutes.case_f,
    ``DivisorGraphRuleH.ForwardRoutes.case_g,
    ``DivisorGraphRuleH.ForwardRoutes.case_h,
    ``DivisorGraphRuleH.ForwardRoutes.case_i,
    ``DivisorGraphRuleH.ForwardRoutes.case_j,
    ``DivisorGraphRuleH.ForwardRoutes.case_k,
    ``DivisorGraphRuleH.ForwardRoutes.forwardH_spec,
    ``DivisorGraphRuleH.RoutePaths.indexSpec_reverse,
    ``DivisorGraphRuleH.RoutePaths.map_indexSpec,
    ``DivisorGraphRuleH.RoutePaths.routeIndices_spec,
    ``DivisorGraphRuleH.Shortening.firstEvenIndex_eq_some_iff,
    ``DivisorGraphRuleH.Shortening.firstEvenIndex_le,
    ``DivisorGraphRuleH.Shortening.firstEven_bounds,
    ``DivisorGraphRuleH.Shortening.no_three_entry_odd_second,
    ``DivisorGraphRuleH.Shortening.suffix_preservation,
    ``DivisorGraphRuleH.OrderedSearch.R1_sound,
    ``DivisorGraphRuleH.OrderedSearch.R2_sound,
    ``DivisorGraphRuleH.OrderedSearch.R3_sound,
    ``DivisorGraphRuleH.OrderedSearch.R4_sound,
    ``DivisorGraphRuleH.OrderedSearch.R5_sound,
    ``DivisorGraphRuleH.OrderedSearch.feasible_endpoints,
    ``DivisorGraphRuleH.OrderedSearch.feasible_ne,
    ``DivisorGraphRuleH.OrderedSearch.link_last,
    ``DivisorGraphRuleH.OrderedSearch.link_zero,
    ``DivisorGraphRuleH.OrderedSearch.mem_R1_iff,
    ``DivisorGraphRuleH.OrderedSearch.mem_R2_iff,
    ``DivisorGraphRuleH.OrderedSearch.mem_R3_iff,
    ``DivisorGraphRuleH.OrderedSearch.mem_R4_iff,
    ``DivisorGraphRuleH.OrderedSearch.mem_R5_iff,
    ``DivisorGraphRuleH.OrderedSearch.mem_freeMultiples_iff,
    ``DivisorGraphRuleH.OrderedSearch.mem_interiorIndices_iff,
    ``DivisorGraphRuleH.OrderedSearch.noLink_valid,
    ``DivisorGraphRuleH.OrderedSearch.options_valid,
    ``DivisorGraphRuleH.OrderedSearch.routesOfKind_sound,
    ``DivisorGraphRuleH.OrderedSearch.search_exists_iff,
    ``DivisorGraphRuleH.OrderedSearch.search_first_iff,
    ``DivisorGraphRuleH.OrderedSearch.search_of_mem_kind,
    ``DivisorGraphRuleH.OrderedSearch.search_sound,
    ``DivisorGraphRuleH.Feasibility.feasible_of_even_one,
    ``DivisorGraphRuleH.Feasibility.universal_feasibility,
    ``DivisorGraphRuleH.RouteExistence.end_present,
    ``DivisorGraphRuleH.RouteExistence.exists_route,
    ``DivisorGraphRuleH.RouteExistence.free_self,
    ``DivisorGraphRuleH.RouteExistence.interior_of_mem,
    ``DivisorGraphRuleH.RouteExistence.lcm_not_dvd_aprime,
    ``DivisorGraphRuleH.RouteExistence.linked_nolink,
    ``DivisorGraphRuleH.RouteExistence.linked_pair,
    ``DivisorGraphRuleH.RouteExistence.nolink_linked,
    ``DivisorGraphRuleH.RouteExistence.nolink_pair,
    ``DivisorGraphRuleH.Offers.beforeB_cons,
    ``DivisorGraphRuleH.Offers.candidate_exists,
    ``DivisorGraphRuleH.Offers.direct_exists,
    ``DivisorGraphRuleH.Offers.direct_or_short,
    ``DivisorGraphRuleH.Offers.firstA_cons,
    ``DivisorGraphRuleH.Offers.firstB_cons,
    ``DivisorGraphRuleH.Offers.offer_exists_iff,
    ``DivisorGraphRuleH.Offers.offer_gain_tie,
    ``DivisorGraphRuleH.Directories.mem_pathPool,
    ``DivisorGraphRuleH.Directories.pathPool_nonempty,
    ``DivisorGraphRuleH.Directories.tablePathAt_of_mem,
    ``DivisorGraphRuleH.SequenceRefinements.A1_eq,
    ``DivisorGraphRuleH.SequenceRefinements.A2_eq,
    ``DivisorGraphRuleH.SequenceRefinements.A3_eq,
    ``DivisorGraphRuleH.SequenceRefinements.B1_eq,
    ``DivisorGraphRuleH.SequenceRefinements.B2_eq,
    ``DivisorGraphRuleH.SequenceRefinements.B3_eq,
    ``DivisorGraphRuleH.SequenceRefinements.Feasible_eq,
    ``DivisorGraphRuleH.SequenceRefinements.H_eq,
    ``DivisorGraphRuleH.SequenceRefinements.R1_eq,
    ``DivisorGraphRuleH.SequenceRefinements.R2_eq,
    ``DivisorGraphRuleH.SequenceRefinements.R3_eq,
    ``DivisorGraphRuleH.SequenceRefinements.R4_eq,
    ``DivisorGraphRuleH.SequenceRefinements.R5_eq,
    ``DivisorGraphRuleH.SequenceRefinements.cofactors_eq,
    ``DivisorGraphRuleH.SequenceRefinements.down_eq,
    ``DivisorGraphRuleH.SequenceRefinements.e_eq,
    ``DivisorGraphRuleH.SequenceRefinements.endOptions_eq,
    ``DivisorGraphRuleH.SequenceRefinements.feasible_eq,
    ``DivisorGraphRuleH.SequenceRefinements.firstEvenIndex_eq,
    ``DivisorGraphRuleH.SequenceRefinements.forwardH_eq,
    ``DivisorGraphRuleH.SequenceRefinements.freeMultiples_eq,
    ``DivisorGraphRuleH.SequenceRefinements.gain_eq,
    ``DivisorGraphRuleH.SequenceRefinements.interiorIndices_eq,
    ``DivisorGraphRuleH.SequenceRefinements.lastIndex_eq,
    ``DivisorGraphRuleH.SequenceRefinements.linkCount_eq,
    ``DivisorGraphRuleH.SequenceRefinements.noLinkEnds_eq,
    ``DivisorGraphRuleH.SequenceRefinements.noLinkStarts_eq,
    ``DivisorGraphRuleH.SequenceRefinements.parity_eq,
    ``DivisorGraphRuleH.SequenceRefinements.rankedRoutes_eq,
    ``DivisorGraphRuleH.SequenceRefinements.routeIndices_eq,
    ``DivisorGraphRuleH.SequenceRefinements.routeOrder_eq,
    ``DivisorGraphRuleH.SequenceRefinements.routesOfKind_eq,
    ``DivisorGraphRuleH.SequenceRefinements.selectedRoute_eq,
    ``DivisorGraphRuleH.SequenceRefinements.shortenedPath_eq,
    ``DivisorGraphRuleH.SequenceRefinements.startOptions_eq,
    ``DivisorGraphRuleH.SequenceRefinements.term_eq,
    ``DivisorGraphRuleH.SequenceRefinements.up_eq,
    ``DivisorGraphRuleH.OfferRefinements.beforeB_eq,
    ``DivisorGraphRuleH.OfferRefinements.beforeB_no_direct,
    ``DivisorGraphRuleH.OfferRefinements.chooseTrace_equal_gain_A,
    ``DivisorGraphRuleH.OfferRefinements.chooseTrace_project,
    ``DivisorGraphRuleH.OfferRefinements.directBlock_eq,
    ``DivisorGraphRuleH.OfferRefinements.firstATrace_project,
    ``DivisorGraphRuleH.OfferRefinements.firstATrace_recomputed,
    ``DivisorGraphRuleH.OfferRefinements.firstATrace_strictly_before,
    ``DivisorGraphRuleH.OfferRefinements.firstA_eq,
    ``DivisorGraphRuleH.OfferRefinements.firstBTrace_project,
    ``DivisorGraphRuleH.OfferRefinements.firstB_eq,
    ``DivisorGraphRuleH.OfferRefinements.firstB_prefix_length,
    ``DivisorGraphRuleH.OfferRefinements.observeOffer_eq,
    ``DivisorGraphRuleH.OfferRefinements.oddPrimeExec_eq,
    ``DivisorGraphRuleH.OfferRefinements.oddPrimeFast_eq,
    ``DivisorGraphRuleH.OfferRefinements.oddPrimeFast_one,
    ``DivisorGraphRuleH.OfferRefinements.offerExec_eq,
    ``DivisorGraphRuleH.OfferRefinements.offerTrace_project,
    ``DivisorGraphRuleH.OfferRefinements.primesUpTo_mem,
    ``DivisorGraphRuleH.OfferRefinements.rowKeyExec_eq,
    ``DivisorGraphRuleH.OfferRefinements.rowKeyFast_eq,
    ``DivisorGraphRuleH.OfferRefinements.shapeKeyExec_eq,
    ``DivisorGraphRuleH.OfferRefinements.shapeKeyFast_eq,
    ``DivisorGraphRuleH.OfferRefinements.shapeOfRow_kind,
    ``DivisorGraphRuleH.OfferRefinements.shapeSizeExec_eq,
    ``DivisorGraphRuleH.OfferRefinements.shapeSizeFast_eq,
    ``DivisorGraphRuleH.OfferRefinements.shortBlock_eq,
    ``DivisorGraphRuleH.OfferRefinements.taggedFindSome_project,
    ``DivisorGraphRuleH.OfferRefinements.taggedFindSome_spec,
    ``DivisorGraphRuleH.OfferRefinements.toSlotExec_eq,
    ``DivisorGraphRuleH.OfferRefinements.toSlotFast_eq,
    ``DivisorGraphRuleH.OfferSoundness.offer_sound,
    ``DivisorGraphRuleH.C_local,
    ``DivisorGraphRuleH.C_offer,
    ``DivisorGraphRuleH.H1,
    ``DivisorGraphRuleH.H2,
    ``DivisorGraphRuleH.H3,
    ``DivisorGraphRuleH.H4,
    ``DivisorGraphRuleH.H5,
    ``DivisorGraphRuleH.H5_directory,
    ``DivisorGraphRuleH.R0
  ]
  for n in results do
    let axioms := (← liftCoreM <| Lean.collectAxioms n).toList
    logInfo m!"REQUIRED_AXIOMS {n}: {axioms}"
    for ax in axioms do
      unless permitted.contains ax do
        logError m!"REQUIRED_AXIOMS_FORBIDDEN {n}: {ax}"
