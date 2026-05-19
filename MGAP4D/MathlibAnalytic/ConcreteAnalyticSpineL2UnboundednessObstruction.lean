import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2DiagonalWeightThreshold

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Obstruction surface for bounded-operator promotion of the concrete diagonal
lane.  This records that the concrete diagonal weights cross every natural
threshold, but it is intentionally not yet an operator-norm unboundedness theorem
and not a closed-operator or self-adjointness theorem. -/
structure ConcreteL2DiagonalUnboundednessObstructionSurface where
  witness : ℕ → ℕ
  thresholdLaw : ∀ k : ℕ, (k : ℝ) < concreteL2DiagonalWeight (witness k)
  inheritedThresholdSurface : concreteAnalyticSpineL2DiagonalWeightThresholdSurfaceReady
  boundaryNotOperatorNormUnboundednessTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop

/-- The concrete diagonal lane has a weight-level obstruction to premature
bounded-operator promotion. -/
def concreteL2DiagonalUnboundednessObstructionSurface :
    ConcreteL2DiagonalUnboundednessObstructionSurface :=
  { witness := concreteL2DiagonalWeightThresholdWitness
    thresholdLaw := concrete_l2_diagonal_weight_threshold_witness_spec
    inheritedThresholdSurface :=
      concrete_analytic_spine_l2_diagonal_weight_threshold_surface_ready
    boundaryNotOperatorNormUnboundednessTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True }

/-- Readiness for the concrete diagonal unboundedness obstruction surface. -/
def concreteAnalyticSpineL2UnboundednessObstructionSurfaceReady : Prop :=
  concreteAnalyticSpineL2DiagonalWeightThresholdSurfaceReady ∧
  (∀ k : ℕ,
    (k : ℝ) < concreteL2DiagonalWeight
      (concreteL2DiagonalUnboundednessObstructionSurface.witness k)) ∧
  concreteL2DiagonalUnboundednessObstructionSurface.boundaryNotOperatorNormUnboundednessTheorem ∧
  concreteL2DiagonalUnboundednessObstructionSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2DiagonalUnboundednessObstructionSurface.boundaryNotSelfAdjointness

/-- Readiness theorem for the concrete diagonal unboundedness obstruction
surface. -/
theorem concrete_analytic_spine_l2_unboundedness_obstruction_surface_ready :
    concreteAnalyticSpineL2UnboundednessObstructionSurfaceReady := by
  unfold concreteAnalyticSpineL2UnboundednessObstructionSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_diagonal_weight_threshold_surface_ready <|
      And.intro concrete_l2_diagonal_weight_threshold_witness_spec <|
        And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the concrete diagonal unboundedness obstruction surface. -/
def concreteAnalyticSpineL2UnboundednessObstructionHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2UnboundednessObstructionSurfaceReady

/-- Boundary theorem for the concrete diagonal unboundedness obstruction surface. -/
theorem concrete_analytic_spine_l2_unboundedness_obstruction_hard_residual_boundary_held :
    concreteAnalyticSpineL2UnboundednessObstructionHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_unboundedness_obstruction_surface_ready

end

end MathlibAnalytic
end MGAP4D
