import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionObligationPacket

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Actual R3 Mathlib-adjoint graph theorem surface.

A graph witness is accepted as the Mathlib-adjoint graph exactly when it is
pointwise identified with both already-proved concrete graph surfaces:

* the completed diagonal graph carrier;
* the formal adjoint graph candidate.

This consumes the previous promotion-obligation packet and turns the named R3
hard point from an obligation marker into a theorem surface. -/
def concreteAnalyticSpineHardResidualR3ActualMathlibAdjointGraphTheorem
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness) : Prop :=
  concreteAnalyticSpineHardResidualR3ActualMathlibGraphPromotionObligationPacket W ∧
  (∀ p : ConcreteL2R2PairSpace,
    W.graph p ↔ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p) ∧
  (∀ p : ConcreteL2R2PairSpace,
    W.graph p ↔ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p) ∧
  concreteAnalyticSpineHardResidualR3FormalAdjointLinearMapGraphEqualsCandidate ∧
  concreteL2R4FormalGraphSelfAdjointness

/-- Every admissible actual-Mathlib graph witness satisfies the adjoint graph
 theorem surface. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_mathlib_adjoint_graph_theorem_ready
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness) :
    concreteAnalyticSpineHardResidualR3ActualMathlibAdjointGraphTheorem W := by
  let hpacket :=
    concrete_analytic_spine_hard_residual_r3_actual_mathlib_graph_promotion_obligation_packet_ready W
  exact ⟨
    hpacket,
    concrete_analytic_spine_hard_residual_r3_promotion_obligation_iff_completed_graph W hpacket,
    concrete_analytic_spine_hard_residual_r3_promotion_obligation_iff_candidate W hpacket,
    concrete_analytic_spine_hard_residual_r3_formal_adjoint_linear_map_graph_eq_candidate,
    concrete_analytic_spine_hard_residual_r3_promotion_obligation_formal_self_adjointness W hpacket⟩

/-- Canonical formal witness version of the R3 Mathlib-adjoint graph theorem. -/
theorem concrete_analytic_spine_hard_residual_r3_canonical_mathlib_adjoint_graph_theorem_ready :
    concreteAnalyticSpineHardResidualR3ActualMathlibAdjointGraphTheorem
      concreteAnalyticSpineHardResidualR3CanonicalFormalGraphWitness := by
  exact concrete_analytic_spine_hard_residual_r3_actual_mathlib_adjoint_graph_theorem_ready
    concreteAnalyticSpineHardResidualR3CanonicalFormalGraphWitness

/-- Projection: the actual Mathlib-adjoint graph theorem identifies the witness
with the completed diagonal graph carrier. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_mathlib_adjoint_graph_theorem_iff_completed
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness)
    (h : concreteAnalyticSpineHardResidualR3ActualMathlibAdjointGraphTheorem W) :
    ∀ p : ConcreteL2R2PairSpace,
      W.graph p ↔ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p := by
  rcases h with ⟨_, hcompleted, _, _, _⟩
  exact hcompleted

/-- Projection: the actual Mathlib-adjoint graph theorem identifies the witness
with the formal adjoint graph candidate. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_mathlib_adjoint_graph_theorem_iff_candidate
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness)
    (h : concreteAnalyticSpineHardResidualR3ActualMathlibAdjointGraphTheorem W) :
    ∀ p : ConcreteL2R2PairSpace,
      W.graph p ↔ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p := by
  rcases h with ⟨_, _, hcandidate, _, _⟩
  exact hcandidate

/-- Projection: the actual Mathlib-adjoint graph theorem carries formal graph
self-adjointness. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_mathlib_adjoint_graph_theorem_formal_self_adjointness
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness)
    (h : concreteAnalyticSpineHardResidualR3ActualMathlibAdjointGraphTheorem W) :
    concreteL2R4FormalGraphSelfAdjointness := by
  rcases h with ⟨_, _, _, _, hformal⟩
  exact hformal

/-- Public post-theorem R3 surface for the Mathlib adjoint graph theorem. -/
def concreteAnalyticSpineHardResidualR3AfterActualMathlibAdjointGraphTheorem : Prop :=
  (∀ W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness,
    concreteAnalyticSpineHardResidualR3ActualMathlibAdjointGraphTheorem W) ∧
  concreteAnalyticSpineHardResidualR3ActualMathlibAdjointGraphTheorem
    concreteAnalyticSpineHardResidualR3CanonicalFormalGraphWitness ∧
  concreteAnalyticSpineHardResidualR3AfterActualMathlibGraphPromotionObligationPacket

/-- The public post-theorem R3 Mathlib adjoint graph surface is ready. -/
theorem concrete_analytic_spine_hard_residual_r3_after_actual_mathlib_adjoint_graph_theorem_ready :
    concreteAnalyticSpineHardResidualR3AfterActualMathlibAdjointGraphTheorem := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_actual_mathlib_adjoint_graph_theorem_ready,
    concrete_analytic_spine_hard_residual_r3_canonical_mathlib_adjoint_graph_theorem_ready,
    concrete_analytic_spine_hard_residual_r3_after_actual_mathlib_graph_promotion_obligation_packet_ready⟩

end

end MathlibAnalytic
end MGAP4D
