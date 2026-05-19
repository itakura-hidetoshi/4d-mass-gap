import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2UnboundednessObstruction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Index surface connecting the diagonal threshold witness to the obstruction
surface witness.  This is bookkeeping for the R2 unbounded-operator lane only:
it is not an operator-norm unboundedness theorem, not graph closure, not a
closed-operator theorem, and not self-adjointness. -/
structure ConcreteL2DiagonalObstructionIndexSurface where
  thresholdSurfaceReady : concreteAnalyticSpineL2DiagonalWeightThresholdSurfaceReady
  obstructionSurfaceReady : concreteAnalyticSpineL2UnboundednessObstructionSurfaceReady
  witnessAgreement : ∀ k : ℕ,
    concreteL2DiagonalUnboundednessObstructionSurface.witness k =
      concreteL2DiagonalWeightThresholdWitness k
  thresholdLaw : ∀ k : ℕ,
    (k : ℝ) < concreteL2DiagonalWeight
      (concreteL2DiagonalUnboundednessObstructionSurface.witness k)
  boundaryNotOperatorNormUnboundednessTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop

/-- The obstruction witness is exactly the threshold witness. -/
theorem concrete_l2_diagonal_obstruction_witness_agrees_with_threshold
    (k : ℕ) :
    concreteL2DiagonalUnboundednessObstructionSurface.witness k =
      concreteL2DiagonalWeightThresholdWitness k := by
  rfl

/-- The obstruction witness satisfies the inherited threshold law. -/
theorem concrete_l2_diagonal_obstruction_index_threshold_law
    (k : ℕ) :
    (k : ℝ) < concreteL2DiagonalWeight
      (concreteL2DiagonalUnboundednessObstructionSurface.witness k) := by
  exact concrete_l2_diagonal_weight_threshold_witness_spec k

/-- Concrete index surface for the l2 diagonal obstruction lane. -/
def concreteL2DiagonalObstructionIndexSurface :
    ConcreteL2DiagonalObstructionIndexSurface :=
  { thresholdSurfaceReady :=
      concrete_analytic_spine_l2_diagonal_weight_threshold_surface_ready
    obstructionSurfaceReady :=
      concrete_analytic_spine_l2_unboundedness_obstruction_surface_ready
    witnessAgreement :=
      concrete_l2_diagonal_obstruction_witness_agrees_with_threshold
    thresholdLaw := concrete_l2_diagonal_obstruction_index_threshold_law
    boundaryNotOperatorNormUnboundednessTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True }

/-- Readiness for the concrete l2 obstruction index surface. -/
def concreteAnalyticSpineL2ObstructionIndexSurfaceReady : Prop :=
  concreteAnalyticSpineL2UnboundednessObstructionSurfaceReady ∧
  (∀ k : ℕ,
    concreteL2DiagonalUnboundednessObstructionSurface.witness k =
      concreteL2DiagonalWeightThresholdWitness k) ∧
  (∀ k : ℕ,
    (k : ℝ) < concreteL2DiagonalWeight
      (concreteL2DiagonalUnboundednessObstructionSurface.witness k)) ∧
  concreteL2DiagonalObstructionIndexSurface.boundaryNotOperatorNormUnboundednessTheorem ∧
  concreteL2DiagonalObstructionIndexSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2DiagonalObstructionIndexSurface.boundaryNotSelfAdjointness

/-- Readiness theorem for the concrete l2 obstruction index surface. -/
theorem concrete_analytic_spine_l2_obstruction_index_surface_ready :
    concreteAnalyticSpineL2ObstructionIndexSurfaceReady := by
  unfold concreteAnalyticSpineL2ObstructionIndexSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_unboundedness_obstruction_surface_ready <|
      And.intro concrete_l2_diagonal_obstruction_witness_agrees_with_threshold <|
        And.intro concrete_l2_diagonal_obstruction_index_threshold_law <|
          And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the concrete l2 obstruction index surface. -/
def concreteAnalyticSpineL2ObstructionIndexHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2ObstructionIndexSurfaceReady

/-- Boundary theorem for the concrete l2 obstruction index surface. -/
theorem concrete_analytic_spine_l2_obstruction_index_hard_residual_boundary_held :
    concreteAnalyticSpineL2ObstructionIndexHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_obstruction_index_surface_ready

end

end MathlibAnalytic
end MGAP4D
