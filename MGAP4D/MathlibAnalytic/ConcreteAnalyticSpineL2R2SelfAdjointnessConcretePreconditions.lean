import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2SelfAdjointnessPreconditionPacket
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CompletedHilbertOperatorNormUnboundedness

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Concrete self-adjointness preconditions that are now actually witnessed in the
completed diagonal operator lane.

This does not assert symmetry, adjoint-domain agreement, essential
self-adjointness, or self-adjointness.  It only promotes the already established
concrete pieces into the self-adjointness lane: real Hilbert carrier, dense
operator surface, closed graph-defined operator, and operator-norm
unboundedness. -/
structure ConcreteL2R2SelfAdjointnessConcretePreconditions where
  baseSelfAdjointnessPreconditionPacketReady :
    concreteAnalyticSpineL2R2SelfAdjointnessPreconditionPacketReady
  realHilbertSpaceReady : concreteL2R2ConcreteRealHilbertSpaceReady
  denselyDefinedOperatorReady : concreteL2R2DenselyDefinedOperatorReady
  completedDiagonalOperatorClosednessReady :
    concreteAnalyticSpineL2R2CompletedDiagonalOperatorClosednessReady
  completedHilbertOperatorNormUnboundednessReady :
    concreteAnalyticSpineL2R2CompletedHilbertOperatorNormUnboundednessReady
  concreteClosedGraphDefinedOperator : concreteL2R2CompletedDiagonalGraphDefinedOperatorClosed
  concreteOperatorNormUnboundedness : concreteL2R2CompletedHilbertOperatorNormUnboundedness
  boundaryNotSymmetryTheorem : Prop
  boundaryNotAdjointDomainAgreementTheorem : Prop
  boundaryNotResolventOrDeficiencyTheorem : Prop
  boundaryNotEssentialSelfAdjointnessTheorem : Prop
  boundaryNotSelfAdjointnessTheorem : Prop
  boundaryNotSpectralTheorem : Prop

/-- Concrete self-adjointness precondition packet for the completed diagonal lane. -/
def concreteL2R2SelfAdjointnessConcretePreconditions :
    ConcreteL2R2SelfAdjointnessConcretePreconditions :=
  { baseSelfAdjointnessPreconditionPacketReady :=
      concrete_analytic_spine_l2_r2_self_adjointness_precondition_packet_ready
    realHilbertSpaceReady :=
      concrete_analytic_spine_l2_r2_concrete_real_hilbert_space_ready
    denselyDefinedOperatorReady :=
      concrete_analytic_spine_l2_r2_densely_defined_operator_ready
    completedDiagonalOperatorClosednessReady :=
      concrete_analytic_spine_l2_r2_completed_diagonal_operator_closedness_ready
    completedHilbertOperatorNormUnboundednessReady :=
      concrete_analytic_spine_l2_r2_completed_hilbert_operator_norm_unboundedness_ready
    concreteClosedGraphDefinedOperator :=
      concrete_l2_r2_completed_diagonal_graph_defined_operator_closed
    concreteOperatorNormUnboundedness :=
      concrete_l2_r2_completed_hilbert_operator_norm_unboundedness
    boundaryNotSymmetryTheorem := True
    boundaryNotAdjointDomainAgreementTheorem := True
    boundaryNotResolventOrDeficiencyTheorem := True
    boundaryNotEssentialSelfAdjointnessTheorem := True
    boundaryNotSelfAdjointnessTheorem := True
    boundaryNotSpectralTheorem := True }

/-- Public theorem-entry predicate for the concrete self-adjointness precondition
upgrade. -/
def concreteAnalyticSpineL2R2SelfAdjointnessConcretePreconditionsReady : Prop :=
  concreteAnalyticSpineL2R2SelfAdjointnessPreconditionPacketReady ∧
  concreteL2R2ConcreteRealHilbertSpaceReady ∧
  concreteL2R2DenselyDefinedOperatorReady ∧
  concreteAnalyticSpineL2R2CompletedDiagonalOperatorClosednessReady ∧
  concreteAnalyticSpineL2R2CompletedHilbertOperatorNormUnboundednessReady ∧
  concreteL2R2CompletedDiagonalGraphDefinedOperatorClosed ∧
  concreteL2R2CompletedHilbertOperatorNormUnboundedness ∧
  True ∧ True ∧ True ∧ True ∧ True ∧ True

/-- The concrete self-adjointness precondition upgrade is ready. -/
theorem concrete_analytic_spine_l2_r2_self_adjointness_concrete_preconditions_ready :
    concreteAnalyticSpineL2R2SelfAdjointnessConcretePreconditionsReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_self_adjointness_precondition_packet_ready,
    concrete_analytic_spine_l2_r2_concrete_real_hilbert_space_ready,
    concrete_analytic_spine_l2_r2_densely_defined_operator_ready,
    concrete_analytic_spine_l2_r2_completed_diagonal_operator_closedness_ready,
    concrete_analytic_spine_l2_r2_completed_hilbert_operator_norm_unboundedness_ready,
    concrete_l2_r2_completed_diagonal_graph_defined_operator_closed,
    concrete_l2_r2_completed_hilbert_operator_norm_unboundedness,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
