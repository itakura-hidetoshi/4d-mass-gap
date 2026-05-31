import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R4VerifiedSelfAdjointnessPreconditionPacket
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2FormalAdjointContainmentAgreementHandoff

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Formal graph-level self-adjointness for the completed diagonal lane.

This is the exact graph-candidate equality statement: the completed diagonal graph
carrier agrees with its formal adjoint graph candidate, together with the already
proved symmetry and formal containment agreement.

This is intentionally not the Mathlib `adjoint` theorem and not an
`IsSelfAdjoint` theorem.  It is the last concrete graph-level surface before the
Mathlib operator/adjointhood interface. -/
def concreteL2R4FormalGraphSelfAdjointness : Prop :=
  concreteL2R4VerifiedSelfAdjointnessPreconditionPacket ∧
  concreteL2R2FormalAdjointContainmentAgreementHandoff ∧
  concreteL2R2CompletedDiagonalGraphSymmetric ∧
  concreteL2R2CompletedDiagonalFormalAdjointContainment ∧
  (concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ⊆
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier) ∧
  (concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier =
    concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate) ∧
  (∀ p : ConcreteL2R2PairSpace,
    p ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier ↔
      p ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate) ∧
  (∀ p : ConcreteL2R2PairSpace,
    p ∈ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph ↔
      p ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier)

/-- Formal graph-level self-adjointness is proved. -/
theorem concrete_l2_r4_formal_graph_self_adjointness :
    concreteL2R4FormalGraphSelfAdjointness := by
  exact ⟨
    concrete_l2_r4_verified_self_adjointness_precondition_packet_ready,
    concrete_l2_r2_formal_adjoint_containment_agreement_handoff_ready,
    concrete_l2_r2_completed_diagonal_graph_symmetric,
    concrete_l2_r2_completed_diagonal_formal_adjoint_containment,
    concrete_l2_r2_formal_adjoint_candidate_reverse_containment_handoff,
    concrete_l2_r2_completed_diagonal_formal_adjoint_graph_agreement_handoff,
    concrete_l2_r2_completed_diagonal_formal_adjoint_graph_mem_iff_handoff,
    concrete_l2_r2_formal_adjoint_linear_map_graph_pointwise_agrees_completed_diagonal⟩

/-- R4 formal-graph self-adjointness boundary.

At this point the formal graph candidate agrees with the completed diagonal graph,
but the Mathlib `adjoint` object, `IsSelfAdjoint`, spectral theorem, PVM, exact
atom, and positive spectral weight have not yet been promoted. -/
def concreteL2R4FormalGraphSelfAdjointnessBoundary : Prop :=
  concreteL2R4FormalGraphSelfAdjointness ∧
  concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness ∧
  concreteL2R2ClosedOperatorBoundaryNotSpectralTheorem ∧
  concreteL2R2ClosedOperatorBoundaryNotPVM ∧
  concreteL2R2ClosedOperatorBoundaryNotPositiveSpectralWeight

/-- The R4 formal-graph self-adjointness boundary is ready. -/
theorem concrete_l2_r4_formal_graph_self_adjointness_boundary_ready :
    concreteL2R4FormalGraphSelfAdjointnessBoundary := by
  exact ⟨
    concrete_l2_r4_formal_graph_self_adjointness,
    concrete_l2_r2_closed_operator_boundary_not_self_adjointness,
    concrete_l2_r2_closed_operator_boundary_not_spectral_theorem,
    concrete_l2_r2_closed_operator_boundary_not_pvm,
    concrete_l2_r2_closed_operator_boundary_not_positive_spectral_weight⟩

/-- Public readiness surface for R4 formal graph-level self-adjointness. -/
def concreteAnalyticSpineL2R4FormalGraphSelfAdjointnessReady : Prop :=
  concreteL2R4FormalGraphSelfAdjointness ∧
  concreteL2R4FormalGraphSelfAdjointnessBoundary

/-- The public R4 formal graph-level self-adjointness surface is ready. -/
theorem concrete_analytic_spine_l2_r4_formal_graph_self_adjointness_ready :
    concreteAnalyticSpineL2R4FormalGraphSelfAdjointnessReady := by
  exact ⟨
    concrete_l2_r4_formal_graph_self_adjointness,
    concrete_l2_r4_formal_graph_self_adjointness_boundary_ready⟩

end

end MathlibAnalytic
end MGAP4D
