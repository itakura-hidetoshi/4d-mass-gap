import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2MathlibOperatorTypeObligationPacket

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Internal graph bridge: the completed diagonal graph carrier and the formal
adjoint graph candidate are identified at graph level, together with both
containment directions.  This remains an internal carrier statement. -/
def concreteL2R2FormalAdjointInternalGraphBridgeReady : Prop :=
  concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier =
    concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ∧
  concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier ⊆
    concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ∧
  concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ⊆
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier

/-- The internal graph-level bridge is ready. -/
theorem concrete_l2_r2_formal_adjoint_internal_graph_bridge_ready :
    concreteL2R2FormalAdjointInternalGraphBridgeReady := by
  exact ⟨
    concrete_l2_r2_completed_diagonal_graph_eq_formal_adjoint_candidate,
    concrete_l2_r2_completed_diagonal_graph_subset_formal_adjoint_candidate,
    concrete_l2_r2_formal_adjoint_candidate_subset_completed_diagonal_graph⟩

/-- Non-promotion bridge: the internal graph bridge and the Mathlib operator API
obligation packet are available, while the Mathlib `adjoint` and
`IsSelfAdjoint` promotion boundaries remain explicitly held. -/
def concreteL2R2FormalAdjointMathlibNonPromotionBridgeReady : Prop :=
  concreteL2R2FormalAdjointInternalGraphBridgeReady ∧
  concreteL2R2AdjointApiTypeObligation ∧
  concreteL2R2MathlibOperatorTypeNoBridgeClaim ∧
  concreteL2R2FormalAdjointBoundaryNotMathlibAdjointIdentifier ∧
  concreteL2R2FormalAdjointBoundaryNotMathlibIsSelfAdjointTheorem

/-- The formal-adjoint/Mathlib non-promotion bridge is ready. -/
theorem concrete_l2_r2_formal_adjoint_mathlib_nonpromotion_bridge_ready :
    concreteL2R2FormalAdjointMathlibNonPromotionBridgeReady := by
  exact ⟨
    concrete_l2_r2_formal_adjoint_internal_graph_bridge_ready,
    concrete_l2_r2_adjoint_api_type_obligation_ready,
    concrete_l2_r2_mathlib_operator_type_no_bridge_claim,
    concrete_l2_r2_formal_adjoint_boundary_not_mathlib_adjoint_identifier,
    concrete_l2_r2_formal_adjoint_boundary_not_mathlib_isSelfAdjoint_theorem⟩

/-- Packet object for the formal-adjoint/Mathlib non-promotion bridge. -/
structure ConcreteL2R2FormalAdjointNonPromotionBridgePacket where
  operatorTypeObligationReady :
    concreteAnalyticSpineL2R2MathlibOperatorTypeObligationPacketReady
  internalGraphBridgeReady : concreteL2R2FormalAdjointInternalGraphBridgeReady
  nonPromotionBridgeReady :
    concreteL2R2FormalAdjointMathlibNonPromotionBridgeReady

/-- Canonical packet instance for the formal-adjoint/Mathlib non-promotion bridge. -/
def concreteL2R2FormalAdjointNonPromotionBridgePacket :
    ConcreteL2R2FormalAdjointNonPromotionBridgePacket :=
  { operatorTypeObligationReady :=
      concrete_analytic_spine_l2_r2_mathlib_operator_type_obligation_packet_ready
    internalGraphBridgeReady :=
      concrete_l2_r2_formal_adjoint_internal_graph_bridge_ready
    nonPromotionBridgeReady :=
      concrete_l2_r2_formal_adjoint_mathlib_nonpromotion_bridge_ready }

/-- Public readiness predicate for the formal-adjoint/Mathlib non-promotion bridge. -/
def concreteAnalyticSpineL2R2FormalAdjointNonPromotionBridgeReady : Prop :=
  concreteAnalyticSpineL2R2MathlibOperatorTypeObligationPacketReady ∧
  concreteL2R2FormalAdjointInternalGraphBridgeReady ∧
  concreteL2R2FormalAdjointMathlibNonPromotionBridgeReady

/-- The formal-adjoint/Mathlib non-promotion bridge surface is ready. -/
theorem concrete_analytic_spine_l2_r2_formal_adjoint_nonpromotion_bridge_ready :
    concreteAnalyticSpineL2R2FormalAdjointNonPromotionBridgeReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_mathlib_operator_type_obligation_packet_ready,
    concrete_l2_r2_formal_adjoint_internal_graph_bridge_ready,
    concrete_l2_r2_formal_adjoint_mathlib_nonpromotion_bridge_ready⟩

end

end MathlibAnalytic
end MGAP4D
