import Mathlib
import RuleHRelease.Definitions.ExecutableSequences
set_option autoImplicit false

theorem DivisorGraphRuleH.SequenceRefinements.lastIndex_eq : DivisorGraphRuleH.Exec.lastIndex = DivisorGraphRuleH.lastIndex := by
  first
  | rfl
  | funext J
    unfold DivisorGraphRuleH.Exec.lastIndex DivisorGraphRuleH.lastIndex
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.term_eq : DivisorGraphRuleH.Exec.term = DivisorGraphRuleH.term := by
  first
  | rfl
  | funext J i
    unfold DivisorGraphRuleH.Exec.term DivisorGraphRuleH.term
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.e_eq : DivisorGraphRuleH.Exec.e = DivisorGraphRuleH.e := by
  funext J k
  exact propext (Nat.even_iff.symm)

theorem DivisorGraphRuleH.SequenceRefinements.parity_eq : DivisorGraphRuleH.Exec.parity = (fun (J : List ℕ) (k : ℕ) => @decide (DivisorGraphRuleH.e J k) (Classical.propDecidable _)) := by
  classical
  funext J k
  simp only [DivisorGraphRuleH.Exec.parity, DivisorGraphRuleH.SequenceRefinements.e_eq]

theorem DivisorGraphRuleH.SequenceRefinements.up_eq : DivisorGraphRuleH.Exec.up = DivisorGraphRuleH.up := by
  first
  | rfl
  | funext lo hi
    unfold DivisorGraphRuleH.Exec.up DivisorGraphRuleH.up
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.down_eq : DivisorGraphRuleH.Exec.down = DivisorGraphRuleH.down := by
  first
  | rfl
  | funext hi lo
    unfold DivisorGraphRuleH.Exec.down DivisorGraphRuleH.down
    rw [DivisorGraphRuleH.SequenceRefinements.up_eq]
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.freeMultiples_eq : DivisorGraphRuleH.Exec.freeMultiples = DivisorGraphRuleH.freeMultiples := by
  first
  | rfl
  | funext J s m
    unfold DivisorGraphRuleH.Exec.freeMultiples DivisorGraphRuleH.freeMultiples
    rw [DivisorGraphRuleH.SequenceRefinements.up_eq]
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.interiorIndices_eq : DivisorGraphRuleH.Exec.interiorIndices = DivisorGraphRuleH.interiorIndices := by
  first
  | rfl
  | funext J m
    unfold DivisorGraphRuleH.Exec.interiorIndices DivisorGraphRuleH.interiorIndices
    rw [DivisorGraphRuleH.SequenceRefinements.lastIndex_eq, DivisorGraphRuleH.SequenceRefinements.term_eq]
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.forwardH_eq : DivisorGraphRuleH.Exec.forwardH = DivisorGraphRuleH.forwardH := by
  funext J u w
  simp only [DivisorGraphRuleH.Exec.forwardH, DivisorGraphRuleH.forwardH,
    DivisorGraphRuleH.Exec.e, DivisorGraphRuleH.e, Nat.even_iff]
  rfl

theorem DivisorGraphRuleH.SequenceRefinements.H_eq : DivisorGraphRuleH.Exec.H = DivisorGraphRuleH.H := by
  first
  | rfl
  | funext J u w
    unfold DivisorGraphRuleH.Exec.H DivisorGraphRuleH.H
    rw [DivisorGraphRuleH.SequenceRefinements.forwardH_eq]
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.Feasible_eq : DivisorGraphRuleH.Exec.Feasible = DivisorGraphRuleH.Feasible := by
  first
  | rfl
  | funext J u w
    unfold DivisorGraphRuleH.Exec.Feasible DivisorGraphRuleH.Feasible
    rw [DivisorGraphRuleH.SequenceRefinements.H_eq]
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.routeIndices_eq : DivisorGraphRuleH.Exec.routeIndices = DivisorGraphRuleH.routeIndices := by
  first
  | rfl
  | funext J u w
    unfold DivisorGraphRuleH.Exec.routeIndices DivisorGraphRuleH.routeIndices
    rw [DivisorGraphRuleH.SequenceRefinements.H_eq]
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.routeOrder_eq : DivisorGraphRuleH.Exec.routeOrder = DivisorGraphRuleH.routeOrder := by
  first
  | rfl
  | funext J u w
    unfold DivisorGraphRuleH.Exec.routeOrder DivisorGraphRuleH.routeOrder
    rw [DivisorGraphRuleH.SequenceRefinements.term_eq, DivisorGraphRuleH.SequenceRefinements.routeIndices_eq]
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.A1_eq : DivisorGraphRuleH.Exec.A1 = DivisorGraphRuleH.A1 := by
  first
  | rfl
  | funext J s slot
    unfold DivisorGraphRuleH.Exec.A1 DivisorGraphRuleH.A1
    rw [DivisorGraphRuleH.SequenceRefinements.lastIndex_eq, DivisorGraphRuleH.SequenceRefinements.freeMultiples_eq]
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.A2_eq : DivisorGraphRuleH.Exec.A2 = DivisorGraphRuleH.A2 := by
  first
  | rfl
  | funext J s slot
    unfold DivisorGraphRuleH.Exec.A2 DivisorGraphRuleH.A2
    rw [DivisorGraphRuleH.SequenceRefinements.lastIndex_eq]
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.A3_eq : DivisorGraphRuleH.Exec.A3 = DivisorGraphRuleH.A3 := by
  first
  | rfl
  | funext J s slot
    unfold DivisorGraphRuleH.Exec.A3 DivisorGraphRuleH.A3
    rw [DivisorGraphRuleH.SequenceRefinements.freeMultiples_eq]
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.B1_eq : DivisorGraphRuleH.Exec.B1 = DivisorGraphRuleH.B1 := by
  first
  | rfl
  | funext J s slot
    unfold DivisorGraphRuleH.Exec.B1 DivisorGraphRuleH.B1
    rw [DivisorGraphRuleH.SequenceRefinements.freeMultiples_eq]
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.B2_eq : DivisorGraphRuleH.Exec.B2 = DivisorGraphRuleH.B2 := by
  first
  | rfl
  | funext J s slot
    unfold DivisorGraphRuleH.Exec.B2 DivisorGraphRuleH.B2
    rw [DivisorGraphRuleH.SequenceRefinements.lastIndex_eq, DivisorGraphRuleH.SequenceRefinements.freeMultiples_eq]
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.B3_eq : DivisorGraphRuleH.Exec.B3 = DivisorGraphRuleH.B3 := by
  first
  | rfl
  | funext J s slot
    unfold DivisorGraphRuleH.Exec.B3 DivisorGraphRuleH.B3
    rw [DivisorGraphRuleH.SequenceRefinements.lastIndex_eq]
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.startOptions_eq : DivisorGraphRuleH.Exec.startOptions = DivisorGraphRuleH.startOptions := by
  first
  | rfl
  | funext J s slot
    unfold DivisorGraphRuleH.Exec.startOptions DivisorGraphRuleH.startOptions
    rw [DivisorGraphRuleH.SequenceRefinements.A1_eq, DivisorGraphRuleH.SequenceRefinements.A2_eq, DivisorGraphRuleH.SequenceRefinements.A3_eq]
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.endOptions_eq : DivisorGraphRuleH.Exec.endOptions = DivisorGraphRuleH.endOptions := by
  first
  | rfl
  | funext J s slot
    unfold DivisorGraphRuleH.Exec.endOptions DivisorGraphRuleH.endOptions
    rw [DivisorGraphRuleH.SequenceRefinements.B1_eq, DivisorGraphRuleH.SequenceRefinements.B2_eq, DivisorGraphRuleH.SequenceRefinements.B3_eq]
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.R1_eq : DivisorGraphRuleH.Exec.R1 = DivisorGraphRuleH.R1 := by
  first
  | rfl
  | funext J s slot
    unfold DivisorGraphRuleH.Exec.R1 DivisorGraphRuleH.R1
    rw [DivisorGraphRuleH.SequenceRefinements.startOptions_eq, DivisorGraphRuleH.SequenceRefinements.endOptions_eq]
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.R2_eq : DivisorGraphRuleH.Exec.R2 = DivisorGraphRuleH.R2 := by
  first
  | rfl
  | funext J s slot
    unfold DivisorGraphRuleH.Exec.R2 DivisorGraphRuleH.R2
    rw [DivisorGraphRuleH.SequenceRefinements.startOptions_eq, DivisorGraphRuleH.SequenceRefinements.endOptions_eq]
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.R3_eq : DivisorGraphRuleH.Exec.R3 = DivisorGraphRuleH.R3 := by
  classical
  funext J s slot
  unfold DivisorGraphRuleH.Exec.R3 DivisorGraphRuleH.R3
  rw [DivisorGraphRuleH.SequenceRefinements.startOptions_eq, DivisorGraphRuleH.SequenceRefinements.interiorIndices_eq]
  apply congrArg (fun f : DivisorGraphRuleH.EndpointOption → List DivisorGraphRuleH.Route =>
    (DivisorGraphRuleH.startOptions J s slot).flatMap f)
  funext A
  cases hA : A.links with
  | none => rfl
  | some xs =>
    apply congrArg (fun f : ℕ → List DivisorGraphRuleH.Route =>
      (DivisorGraphRuleH.interiorIndices J slot.a').flatMap f)
    funext w
    exact ite_congr
      (congrFun (congrFun (congrFun DivisorGraphRuleH.SequenceRefinements.Feasible_eq J) A.index) w)
      (fun _ => rfl) (fun _ => rfl)

theorem DivisorGraphRuleH.SequenceRefinements.R4_eq : DivisorGraphRuleH.Exec.R4 = DivisorGraphRuleH.R4 := by
  classical
  funext J s slot
  unfold DivisorGraphRuleH.Exec.R4 DivisorGraphRuleH.R4
  rw [DivisorGraphRuleH.SequenceRefinements.endOptions_eq, DivisorGraphRuleH.SequenceRefinements.interiorIndices_eq]
  apply congrArg (fun f : ℕ → List DivisorGraphRuleH.Route =>
    (DivisorGraphRuleH.interiorIndices J slot.a).flatMap f)
  funext u
  apply congrArg (fun f : DivisorGraphRuleH.EndpointOption → List DivisorGraphRuleH.Route =>
    (DivisorGraphRuleH.endOptions J s slot).flatMap f)
  funext B
  cases hB : B.links with
  | none => rfl
  | some ys =>
    exact ite_congr
      (congrFun (congrFun (congrFun DivisorGraphRuleH.SequenceRefinements.Feasible_eq J) u) B.index)
      (fun _ => rfl) (fun _ => rfl)

theorem DivisorGraphRuleH.SequenceRefinements.noLinkStarts_eq : DivisorGraphRuleH.Exec.noLinkStarts = DivisorGraphRuleH.noLinkStarts := by
  first
  | rfl
  | funext J s slot
    unfold DivisorGraphRuleH.Exec.noLinkStarts DivisorGraphRuleH.noLinkStarts
    rw [DivisorGraphRuleH.SequenceRefinements.interiorIndices_eq, DivisorGraphRuleH.SequenceRefinements.startOptions_eq]
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.noLinkEnds_eq : DivisorGraphRuleH.Exec.noLinkEnds = DivisorGraphRuleH.noLinkEnds := by
  first
  | rfl
  | funext J s slot
    unfold DivisorGraphRuleH.Exec.noLinkEnds DivisorGraphRuleH.noLinkEnds
    rw [DivisorGraphRuleH.SequenceRefinements.interiorIndices_eq, DivisorGraphRuleH.SequenceRefinements.endOptions_eq]
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.R5_eq : DivisorGraphRuleH.Exec.R5 = DivisorGraphRuleH.R5 := by
  classical
  funext J s slot
  unfold DivisorGraphRuleH.Exec.R5 DivisorGraphRuleH.R5
  rw [DivisorGraphRuleH.SequenceRefinements.noLinkStarts_eq, DivisorGraphRuleH.SequenceRefinements.noLinkEnds_eq]
  apply congrArg (fun f : ℕ → List DivisorGraphRuleH.Route =>
    (DivisorGraphRuleH.noLinkStarts J s slot).flatMap f)
  funext u
  apply congrArg (fun f : ℕ → List DivisorGraphRuleH.Route =>
    (DivisorGraphRuleH.noLinkEnds J s slot).flatMap f)
  funext w
  exact ite_congr
    (congrArg (fun p : Prop => u ≠ w ∧ p)
      (congrFun (congrFun (congrFun DivisorGraphRuleH.SequenceRefinements.Feasible_eq J) u) w))
    (fun _ => rfl) (fun _ => rfl)

theorem DivisorGraphRuleH.SequenceRefinements.routesOfKind_eq : DivisorGraphRuleH.Exec.routesOfKind = DivisorGraphRuleH.routesOfKind := by
  first
  | rfl
  | funext J s slot kind
    cases kind <;> simp only [DivisorGraphRuleH.Exec.routesOfKind, DivisorGraphRuleH.routesOfKind, DivisorGraphRuleH.SequenceRefinements.R1_eq, DivisorGraphRuleH.SequenceRefinements.R2_eq, DivisorGraphRuleH.SequenceRefinements.R3_eq, DivisorGraphRuleH.SequenceRefinements.R4_eq, DivisorGraphRuleH.SequenceRefinements.R5_eq]

theorem DivisorGraphRuleH.SequenceRefinements.rankedRoutes_eq : DivisorGraphRuleH.Exec.rankedRoutes = DivisorGraphRuleH.rankedRoutes := by
  funext J s slot
  simp only [DivisorGraphRuleH.Exec.rankedRoutes, DivisorGraphRuleH.rankedRoutes, DivisorGraphRuleH.SequenceRefinements.routesOfKind_eq]

theorem DivisorGraphRuleH.SequenceRefinements.selectedRoute_eq : DivisorGraphRuleH.Exec.selectedRoute = DivisorGraphRuleH.selectedRoute := by
  first
  | rfl
  | funext J s slot
    unfold DivisorGraphRuleH.Exec.selectedRoute DivisorGraphRuleH.selectedRoute
    rw [DivisorGraphRuleH.SequenceRefinements.rankedRoutes_eq]
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.cofactors_eq : DivisorGraphRuleH.Exec.cofactors = DivisorGraphRuleH.cofactors := by
  first
  | rfl
  | funext J r
    unfold DivisorGraphRuleH.Exec.cofactors DivisorGraphRuleH.cofactors
    rw [DivisorGraphRuleH.SequenceRefinements.routeOrder_eq]
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.linkCount_eq : DivisorGraphRuleH.Exec.linkCount = DivisorGraphRuleH.linkCount := by
  first
  | rfl
  | funext r
    unfold DivisorGraphRuleH.Exec.linkCount DivisorGraphRuleH.linkCount
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.gain_eq : DivisorGraphRuleH.Exec.gain = DivisorGraphRuleH.gain := by
  first
  | rfl
  | funext J r
    unfold DivisorGraphRuleH.Exec.gain DivisorGraphRuleH.gain
    rw [DivisorGraphRuleH.SequenceRefinements.linkCount_eq]
    all_goals rfl

theorem DivisorGraphRuleH.SequenceRefinements.firstEvenIndex_eq : DivisorGraphRuleH.Exec.firstEvenIndex = DivisorGraphRuleH.firstEvenIndex := by
  funext J
  exact congrArg (fun p : ℕ → Bool => (List.range J.length).find? p)
    (congrFun DivisorGraphRuleH.SequenceRefinements.parity_eq J)

theorem DivisorGraphRuleH.SequenceRefinements.shortenedPath_eq : DivisorGraphRuleH.Exec.shortenedPath = DivisorGraphRuleH.shortenedPath := by
  funext J
  simp only [DivisorGraphRuleH.Exec.shortenedPath, DivisorGraphRuleH.shortenedPath,
    DivisorGraphRuleH.Exec.e, DivisorGraphRuleH.e, Nat.even_iff, DivisorGraphRuleH.SequenceRefinements.firstEvenIndex_eq]
  rfl

theorem DivisorGraphRuleH.SequenceRefinements.feasible_eq : DivisorGraphRuleH.Exec.feasible = (fun (J : List ℕ) (u w : ℕ) => @decide (DivisorGraphRuleH.Feasible J u w) (Classical.propDecidable _)) := by
  classical
  funext J u w
  unfold DivisorGraphRuleH.Exec.feasible DivisorGraphRuleH.Feasible
  rw [DivisorGraphRuleH.SequenceRefinements.H_eq]
  cases (DivisorGraphRuleH.H J u w).isSome <;> simp


def DivisorGraphRuleH.SequenceRefinements.results : Unit := ()
