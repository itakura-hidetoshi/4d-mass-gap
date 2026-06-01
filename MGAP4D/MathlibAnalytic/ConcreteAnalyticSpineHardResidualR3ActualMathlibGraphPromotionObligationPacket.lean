import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionTargetContract

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Obligation packet for the future genuine Mathlib self-adjointness promotion.

The packet gathers every already-proved graph input and keeps the current
non-promotion boundary visible.  A later proof can consume this packet, but this
packet itself does not claim the promoted Mathlib self-adjointness result. -/
def concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionObligationPacket
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness) : Prop :=
  concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionTargetContract W ∧
  concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionTargetInput W ∧
  concreteAnalyticSpineHardResidualR3ActualMathlibGraphWitnessClosedPreInput W ∧
  (∀ p : ConcreteL2R2PairSpace,
    W.graph p ↔ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p) ∧
  (∀ p : ConcreteL2R2PairSpace,
    W.graph p ↔ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p) ∧
  concreteL2R4FormalGraphSelfAdjointness ∧
  concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness

/-- The promotion obligation packet is ready for every witness. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_mathlib_graph_promotion_obligation_packet_ready
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness) :
    concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionObligationPacket W := by
  let htarget :=
    concrete_analytic_spine_hard_residual_r3_actual_mathlib_graph_promotion_target_input_ready W
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_actual_mathlib_graph_promotion_target_contract_ready W,
    htarget,
    concrete_analytic_spine_hard_residual_r3_promotion_target_input_closed_preinput W htarget,
    concrete_analytic_spine_hard_residual_r3_promotion_target_input_iff_completed_graph W htarget,
    concrete_analytic_spine_hard_residual_r3_promotion_target_input_iff_candidate W htarget,
    concrete_analytic_spine_hard_residual_r3_promotion_target_input_formal_self_adjointness W htarget,
    concrete_analytic_spine_hard_residual_r3_promotion_target_input_boundary_not_self_adjointness W htarget⟩

/-- Elimination: the obligation packet exposes the promotion target contract. -/
theorem concrete_analytic_spine_hard_residual_r3_promotion_obligation_target_contract
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness)
    (h : concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionObligationPacket W) :
    concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionTargetContract W := by
  rcases h with ⟨htarget, _, _, _, _, _, _⟩
  exact htarget

/-- Elimination: the obligation packet exposes the promotion target input. -/
theorem concrete_analytic_spine_hard_residual_r3_promotion_obligation_target_input
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness)
    (h : concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionObligationPacket W) :
    concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionTargetInput W := by
  rcases h with ⟨_, hinput, _, _, _, _, _⟩
  exact hinput

/-- Elimination: the obligation packet exposes the completed graph carrier iff. -/
theorem concrete_analytic_spine_hard_residual_r3_promotion_obligation_iff_completed_graph
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness)
    (h : concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionObligationPacket W) :
    ∀ p : ConcreteL2R2PairSpace,
      W.graph p ↔ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p := by
  rcases h with ⟨_, _, _, hcompleted, _, _, _⟩
  exact hcompleted

/-- Elimination: the obligation packet exposes the formal candidate graph iff. -/
theorem concrete_analytic_spine_hard_residual_r3_promotion_obligation_iff_candidate
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness)
    (h : concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionObligationPacket W) :
    ∀ p : ConcreteL2R2PairSpace,
      W.graph p ↔ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p := by
  rcases h with ⟨_, _, _, _, hcandidate, _, _⟩
  exact hcandidate

/-- Elimination: the obligation packet exposes formal graph self-adjointness. -/
theorem concrete_analytic_spine_hard_residual_r3_promotion_obligation_formal_self_adjointness
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness)
    (h : concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionObligationPacket W) :
    concreteL2R4FormalGraphSelfAdjointness := by
  rcases h with ⟨_, _, _, _, _, hformal, _⟩
  exact hformal

/-- Elimination: the obligation packet exposes the still-held non-promotion boundary. -/
theorem concrete_analytic_spine_hard_residual_r3_promotion_obligation_boundary_not_self_adjointness
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness)
    (h : concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionObligationPacket W) :
    concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness := by
  rcases h with ⟨_, _, _, _, _, _, hboundary⟩
  exact hboundary

/-- Canonical formal witness obligation packet. -/
theorem concrete_analytic_spine_hard_residual_r3_canonical_formal_graph_promotion_obligation_packet_ready :
    concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionObligationPacket
      concreteAnalyticSpineHardResidualR3CanonicalFormalGraphWitness := by
  exact concrete_analytic_spine_hard_residual_r3_actual_mathlib_graph_promotion_obligation_packet_ready
    concreteAnalyticSpineHardResidualR3CanonicalFormalGraphWitness

/-- R3 after promotion-obligation packetization. -/
def concreteAnalyticSpineHardResidualR3AfterActualMathlibGraphPromotionObligationPacket : Prop :=
  (∀ W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness,
    concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionObligationPacket W) ∧
  concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionObligationPacket
    concreteAnalyticSpineHardResidualR3CanonicalFormalGraphWitness ∧
  concreteAnalyticSpineHardResidualR3AfterActualMathlibGraphPromotionTargetContract

/-- The post-promotion-obligation-packet R3 surface is ready. -/
theorem concrete_analytic_spine_hard_residual_r3_after_actual_mathlib_graph_promotion_obligation_packet_ready :
    concreteAnalyticSpineHardResidualR3AfterActualMathlibGraphPromotionObligationPacket := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_actual_mathlib_graph_promotion_obligation_packet_ready,
    concrete_analytic_spine_hard_residual_r3_canonical_formal_graph_promotion_obligation_packet_ready,
    concrete_analytic_spine_hard_residual_r3_after_actual_mathlib_graph_promotion_target_contract_ready⟩

end

end MathlibAnalytic
end MGAP4D
