import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2FormalAdjointSelfAdjointPreconditionHandoff
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2AdjointContainmentSurface

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Reverse containment at the formal graph-candidate level: every formal-adjoint
candidate point is already a point of the completed diagonal graph carrier.

This is still a graph-candidate statement, not a Mathlib adjoint theorem. -/
theorem concrete_l2_r2_formal_adjoint_candidate_reverse_containment_handoff :
    concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ⊆
      concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier := by
  exact concrete_l2_r2_formal_adjoint_candidate_subset_completed_diagonal_graph

/-- Forward containment at the formal graph-candidate level, i.e. the already
established adjoint-containment surface. -/
theorem concrete_l2_r2_completed_diagonal_forward_formal_adjoint_containment_handoff :
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier ⊆
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  exact concrete_l2_r2_completed_diagonal_graph_subset_formal_adjoint_candidate

/-- Bidirectional graph agreement between the completed diagonal graph carrier and
the formal-adjoint graph candidate. -/
theorem concrete_l2_r2_completed_diagonal_formal_adjoint_graph_agreement_handoff :
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier =
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  exact concrete_l2_r2_completed_diagonal_graph_eq_formal_adjoint_candidate

/-- Elementwise version of the graph agreement handoff. -/
theorem concrete_l2_r2_completed_diagonal_formal_adjoint_graph_mem_iff_handoff
    (p : ConcreteL2R2PairSpace) :
    p ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier ↔
      p ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  rw [concrete_l2_r2_completed_diagonal_formal_adjoint_graph_agreement_handoff]

/-- Formal-adjoint containment agreement handoff.

This consolidates the forward containment surface, reverse formal graph-candidate
containment, graph equality, closed graph transfer, and self-adjointness
precondition handoff.  It deliberately remains below Mathlib `adjoint` /
`IsSelfAdjoint`: the agreement is still expressed at the concrete graph-candidate
level. -/
def concreteL2R2FormalAdjointContainmentAgreementHandoff : Prop :=
  concreteAnalyticSpineL2R2AdjointContainmentSurfaceReady ∧
  concreteAnalyticSpineL2R2FormalAdjointSelfAdjointnessPreconditionHandoffReady ∧
  concreteL2R2CompletedDiagonalFormalAdjointContainment ∧
  (concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ⊆
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier) ∧
  (concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier =
    concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate) ∧
  (∀ p : ConcreteL2R2PairSpace,
    p ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier ↔
      p ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate) ∧
  concreteL2R2FormalAdjointClosedOperatorGraphEquivalence ∧
  concreteL2R2FormalAdjointSelfAdjointnessPreconditionHandoff

/-- The formal-adjoint containment agreement handoff is ready. -/
theorem concrete_l2_r2_formal_adjoint_containment_agreement_handoff_ready :
    concreteL2R2FormalAdjointContainmentAgreementHandoff := by
  exact ⟨
    concrete_analytic_spine_l2_r2_adjoint_containment_surface_ready,
    concrete_analytic_spine_l2_r2_formal_adjoint_self_adjointness_precondition_handoff_ready,
    concrete_l2_r2_completed_diagonal_formal_adjoint_containment,
    concrete_l2_r2_formal_adjoint_candidate_reverse_containment_handoff,
    concrete_l2_r2_completed_diagonal_formal_adjoint_graph_agreement_handoff,
    concrete_l2_r2_completed_diagonal_formal_adjoint_graph_mem_iff_handoff,
    concrete_l2_r2_formal_adjoint_closed_operator_graph_equivalence_ready,
    concrete_l2_r2_formal_adjoint_self_adjointness_precondition_handoff_ready⟩

/-- Public readiness predicate for the formal-adjoint containment agreement
handoff. -/
def concreteAnalyticSpineL2R2FormalAdjointContainmentAgreementHandoffReady : Prop :=
  concreteL2R2FormalAdjointContainmentAgreementHandoff

/-- The public readiness predicate for the formal-adjoint containment agreement
handoff is ready. -/
theorem concrete_analytic_spine_l2_r2_formal_adjoint_containment_agreement_handoff_ready :
    concreteAnalyticSpineL2R2FormalAdjointContainmentAgreementHandoffReady := by
  exact concrete_l2_r2_formal_adjoint_containment_agreement_handoff_ready

end

end MathlibAnalytic
end MGAP4D
