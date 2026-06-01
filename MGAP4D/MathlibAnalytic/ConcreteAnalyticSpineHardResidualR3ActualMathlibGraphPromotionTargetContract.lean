import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitnessHandoffEliminators

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Promotion target input for the future genuine Mathlib self-adjointness proof.

This is not the promoted theorem itself.  It is the fully named input surface that
must be consumed by the later proof which removes the current non-promotion
boundary and establishes the actual Mathlib self-adjointness predicate. -/
def concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionTargetInput
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness) : Prop :=
  concreteAnalyticSpineHardResidualR3ActualMathlibGraphWitnessPromotionBoundaryPacket W ∧
  concreteAnalyticSpineHardResidualR3ActualMathlibGraphWitnessClosedPreInput W ∧
  (∀ p : ConcreteL2R2PairSpace,
    W.graph p ↔ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p) ∧
  (∀ p : ConcreteL2R2PairSpace,
    W.graph p ↔ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p) ∧
  concreteL2R4FormalGraphSelfAdjointness ∧
  concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness

/-- The promotion target input is ready for every actual Mathlib graph witness. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_mathlib_graph_promotion_target_input_ready
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness) :
    concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionTargetInput W := by
  let h :=
    concrete_analytic_spine_hard_residual_r3_actual_mathlib_graph_witness_promotion_boundary_packet_ready W
  exact ⟨
    h,
    concrete_analytic_spine_hard_residual_r3_witness_handoff_closed_preinput W h.1,
    concrete_analytic_spine_hard_residual_r3_witness_handoff_iff_completed_graph W h.1,
    concrete_analytic_spine_hard_residual_r3_witness_handoff_iff_candidate W h.1,
    concrete_analytic_spine_hard_residual_r3_witness_handoff_formal_self_adjointness W h.1,
    concrete_analytic_spine_hard_residual_r3_witness_handoff_boundary_not_self_adjointness W h.1⟩

/-- Elimination: the promotion target input exposes the boundary packet. -/
theorem concrete_analytic_spine_hard_residual_r3_promotion_target_input_boundary_packet
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness)
    (h : concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionTargetInput W) :
    concreteAnalyticSpineHardResidualR3ActualMathlibGraphWitnessPromotionBoundaryPacket W := by
  rcases h with ⟨hpacket, _, _, _, _, _⟩
  exact hpacket

/-- Elimination: the promotion target input exposes the closed pre-input. -/
theorem concrete_analytic_spine_hard_residual_r3_promotion_target_input_closed_preinput
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness)
    (h : concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionTargetInput W) :
    concreteAnalyticSpineHardResidualR3ActualMathlibGraphWitnessClosedPreInput W := by
  rcases h with ⟨_, hclosed, _, _, _, _⟩
  exact hclosed

/-- Elimination: the promotion target input exposes graph equivalence with the
completed graph carrier. -/
theorem concrete_analytic_spine_hard_residual_r3_promotion_target_input_iff_completed_graph
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness)
    (h : concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionTargetInput W) :
    ∀ p : ConcreteL2R2PairSpace,
      W.graph p ↔ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p := by
  rcases h with ⟨_, _, hcompleted, _, _, _⟩
  exact hcompleted

/-- Elimination: the promotion target input exposes graph equivalence with the
formal adjoint candidate graph. -/
theorem concrete_analytic_spine_hard_residual_r3_promotion_target_input_iff_candidate
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness)
    (h : concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionTargetInput W) :
    ∀ p : ConcreteL2R2PairSpace,
      W.graph p ↔ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p := by
  rcases h with ⟨_, _, _, hcandidate, _, _⟩
  exact hcandidate

/-- Elimination: the promotion target input exposes formal graph self-adjointness. -/
theorem concrete_analytic_spine_hard_residual_r3_promotion_target_input_formal_self_adjointness
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness)
    (h : concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionTargetInput W) :
    concreteL2R4FormalGraphSelfAdjointness := by
  rcases h with ⟨_, _, _, _, hformal, _⟩
  exact hformal

/-- Elimination: the promotion target input keeps the non-promotion boundary visible. -/
theorem concrete_analytic_spine_hard_residual_r3_promotion_target_input_boundary_not_self_adjointness
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness)
    (h : concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionTargetInput W) :
    concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness := by
  rcases h with ⟨_, _, _, _, _, hboundary⟩
  exact hboundary

/-- Final promotion contract surface.

The first conjunct is the named input surface for the future promotion theorem.
The second conjunct deliberately records that the current state is still a
non-promotion boundary, so a later commit must replace this contract with a real
Mathlib self-adjointness theorem rather than silently treating the formal graph
surface as promoted. -/
def concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionTargetContract
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness) : Prop :=
  concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionTargetInput W ∧
  concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness

/-- The promotion target contract is ready for every witness. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_mathlib_graph_promotion_target_contract_ready
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness) :
    concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionTargetContract W := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_actual_mathlib_graph_promotion_target_input_ready W,
    concrete_l2_r2_closed_operator_boundary_not_self_adjointness⟩

/-- R3 after promotion target contract: the formal input side is ready and the
remaining gap is explicitly the Mathlib self-adjointness promotion proof. -/
def concreteAnalyticSpineHardResidualR3AfterActualMathlibGraphPromotionTargetContract : Prop :=
  (∀ W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness,
    concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionTargetContract W) ∧
  concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionTargetContract
    concreteAnalyticSpineHardResidualR3CanonicalFormalGraphWitness ∧
  concreteAnalyticSpineHardResidualR3AfterActualMathlibGraphWitnessHandoffEliminators

/-- The post-promotion-target-contract R3 surface is ready. -/
theorem concrete_analytic_spine_hard_residual_r3_after_actual_mathlib_graph_promotion_target_contract_ready :
    concreteAnalyticSpineHardResidualR3AfterActualMathlibGraphPromotionTargetContract := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_actual_mathlib_graph_promotion_target_contract_ready,
    concrete_analytic_spine_hard_residual_r3_actual_mathlib_graph_promotion_target_contract_ready
      concreteAnalyticSpineHardResidualR3CanonicalFormalGraphWitness,
    concrete_analytic_spine_hard_residual_r3_after_actual_mathlib_graph_witness_handoff_eliminators_ready⟩

end

end MathlibAnalytic
end MGAP4D
