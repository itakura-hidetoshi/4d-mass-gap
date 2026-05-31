import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R3ClosedGraphPromotion
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2SelfAdjointnessConcretePreconditions
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2FormalAdjointSelfAdjointPreconditionHandoff

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- R3-to-R4 precondition lane.

R3 supplies the direct closed-graph promotion for the original diagonal graph.
R4 begins only after the self-adjointness lane has concrete preconditions and the
formal-adjoint handoff has symmetry, graph agreement, domain agreement, and
coordinate-value agreement.

This is still a precondition handoff, not a Mathlib `adjoint` theorem and not a
self-adjointness theorem. -/
def concreteL2R3ToR4SelfAdjointnessPreconditionHandoff : Prop :=
  concreteAnalyticSpineL2R3ClosedGraphPromotionReady ∧
  concreteAnalyticSpineL2R2SelfAdjointnessConcretePreconditionsReady ∧
  concreteAnalyticSpineL2R2FormalAdjointSelfAdjointnessPreconditionHandoffReady

/-- The R3-to-R4 self-adjointness precondition handoff is ready. -/
theorem concrete_l2_r3_to_r4_self_adjointness_precondition_handoff_ready :
    concreteL2R3ToR4SelfAdjointnessPreconditionHandoff := by
  exact ⟨
    concrete_analytic_spine_l2_r3_closed_graph_promotion_ready,
    concrete_analytic_spine_l2_r2_self_adjointness_concrete_preconditions_ready,
    concrete_analytic_spine_l2_r2_formal_adjoint_self_adjointness_precondition_handoff_ready⟩

/-- R4 pre-self-adjointness packet.

This packet records that the project has crossed the R3 closed-graph threshold and
has gathered the formal-adjoint preconditions needed before attempting a genuine
Mathlib self-adjointness theorem. -/
def concreteL2R4PreSelfAdjointnessPacket : Prop :=
  concreteL2R3ToR4SelfAdjointnessPreconditionHandoff ∧
  concreteL2R3ClosedGraphPromotionBoundary ∧
  concreteL2R2FormalAdjointSelfAdjointnessPreconditionHandoff

/-- The R4 pre-self-adjointness packet is ready. -/
theorem concrete_l2_r4_pre_self_adjointness_packet_ready :
    concreteL2R4PreSelfAdjointnessPacket := by
  exact ⟨
    concrete_l2_r3_to_r4_self_adjointness_precondition_handoff_ready,
    concrete_l2_r3_closed_graph_promotion_boundary_ready,
    concrete_l2_r2_formal_adjoint_self_adjointness_precondition_handoff_ready⟩

/-- R4 boundary: even after the pre-self-adjointness packet, this is not yet the
Mathlib adjoint graph theorem, not yet self-adjointness, not yet spectral theorem,
not yet PVM, and not yet positive spectral weight. -/
def concreteL2R4PreSelfAdjointnessBoundary : Prop :=
  concreteL2R4PreSelfAdjointnessPacket ∧
  concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness ∧
  concreteL2R2ClosedOperatorBoundaryNotSpectralTheorem ∧
  concreteL2R2ClosedOperatorBoundaryNotPVM ∧
  concreteL2R2ClosedOperatorBoundaryNotPositiveSpectralWeight

/-- The R4 pre-self-adjointness boundary is ready. -/
theorem concrete_l2_r4_pre_self_adjointness_boundary_ready :
    concreteL2R4PreSelfAdjointnessBoundary := by
  exact ⟨
    concrete_l2_r4_pre_self_adjointness_packet_ready,
    concrete_l2_r2_closed_operator_boundary_not_self_adjointness,
    concrete_l2_r2_closed_operator_boundary_not_spectral_theorem,
    concrete_l2_r2_closed_operator_boundary_not_pvm,
    concrete_l2_r2_closed_operator_boundary_not_positive_spectral_weight⟩

/-- Public readiness surface for the R3-to-R4 self-adjointness precondition handoff. -/
def concreteAnalyticSpineL2R3ToR4SelfAdjointnessPreconditionHandoffReady : Prop :=
  concreteL2R4PreSelfAdjointnessPacket ∧
  concreteL2R4PreSelfAdjointnessBoundary

/-- The public R3-to-R4 self-adjointness precondition handoff is ready. -/
theorem concrete_analytic_spine_l2_r3_to_r4_self_adjointness_precondition_handoff_ready :
    concreteAnalyticSpineL2R3ToR4SelfAdjointnessPreconditionHandoffReady := by
  exact ⟨
    concrete_l2_r4_pre_self_adjointness_packet_ready,
    concrete_l2_r4_pre_self_adjointness_boundary_ready⟩

end

end MathlibAnalytic
end MGAP4D
