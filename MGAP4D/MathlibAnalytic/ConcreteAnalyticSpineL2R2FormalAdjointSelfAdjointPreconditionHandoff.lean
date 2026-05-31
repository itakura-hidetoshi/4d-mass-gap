import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2FormalAdjointClosedOperatorHandoff
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2SymmetricOperatorSurface
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2SelfAdjointnessPreconditionPacket

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Symmetry of the formal-adjoint `LinearMap` graph presentation, transported
from the completed diagonal graph symmetry through graph equality. -/
theorem concrete_l2_r2_formal_adjoint_linear_map_graph_symmetric :
    ∀ {x Tx z Tz : lp (fun _ : ℕ => ℝ) 2},
      (x, Tx) ∈ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph →
      (z, Tz) ∈ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph →
      inner ℝ Tx z = inner ℝ x Tz := by
  intro x Tx z Tz hxgraph hzgraph
  have hxdiag : (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier :=
    (concrete_l2_r2_formal_adjoint_linear_map_graph_mem_iff_completed_diagonal_graph
      (x, Tx)).1 hxgraph
  have hzdiag : (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier :=
    (concrete_l2_r2_formal_adjoint_linear_map_graph_mem_iff_completed_diagonal_graph
      (z, Tz)).1 hzgraph
  exact concrete_l2_r2_completed_diagonal_graph_symmetric hxdiag hzdiag

/-- Symmetry of the formal-adjoint graph candidate, transported from the completed
diagonal graph symmetry through graph equality. -/
theorem concrete_l2_r2_formal_adjoint_graph_candidate_symmetric :
    ∀ {x Tx z Tz : lp (fun _ : ℕ => ℝ) 2},
      (x, Tx) ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate →
      (z, Tz) ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate →
      inner ℝ Tx z = inner ℝ x Tz := by
  intro x Tx z Tz hxgraph hzgraph
  have hxdiag : (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier :=
    (concrete_l2_r2_formal_adjoint_candidate_mem_iff_completed_diagonal_graph
      (x, Tx)).1 hxgraph
  have hzdiag : (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier :=
    (concrete_l2_r2_formal_adjoint_candidate_mem_iff_completed_diagonal_graph
      (z, Tz)).1 hzgraph
  exact concrete_l2_r2_completed_diagonal_graph_symmetric hxdiag hzdiag

/-- Pointwise agreement between the formal-adjoint `LinearMap` graph and the
completed diagonal graph carrier. -/
theorem concrete_l2_r2_formal_adjoint_linear_map_graph_pointwise_agrees_completed_diagonal :
    ∀ p : ConcreteL2R2PairSpace,
      p ∈ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph ↔
        p ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier := by
  intro p
  exact concrete_l2_r2_formal_adjoint_linear_map_graph_mem_iff_completed_diagonal_graph p

/-- Pointwise agreement between the formal-adjoint graph candidate and the
completed diagonal graph carrier. -/
theorem concrete_l2_r2_formal_adjoint_graph_candidate_pointwise_agrees_completed_diagonal :
    ∀ p : ConcreteL2R2PairSpace,
      p ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ↔
        p ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier := by
  intro p
  exact concrete_l2_r2_formal_adjoint_candidate_mem_iff_completed_diagonal_graph p

/-- Formal-adjoint self-adjointness precondition handoff.

This handoff still does not assert Mathlib `adjoint`, `IsSelfAdjoint`, spectral
measure, PVM, or positive spectral weight.  It records the proved ingredients
available before that promotion: closed graph transfer, graph equivalence, and
symmetry transported to the formal-adjoint `LinearMap` graph presentation. -/
def concreteL2R2FormalAdjointSelfAdjointnessPreconditionHandoff : Prop :=
  concreteAnalyticSpineL2R2SelfAdjointnessPreconditionPacketReady ∧
  concreteL2R2FormalAdjointClosedOperatorHandoff ∧
  concreteL2R2FormalAdjointClosedOperatorGraphEquivalence ∧
  concreteL2R2FormalAdjointLinearMapClosedGraphTransfer ∧
  (∀ {x Tx z Tz : lp (fun _ : ℕ => ℝ) 2},
    (x, Tx) ∈ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph →
    (z, Tz) ∈ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph →
    inner ℝ Tx z = inner ℝ x Tz) ∧
  (∀ {x Tx z Tz : lp (fun _ : ℕ => ℝ) 2},
    (x, Tx) ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate →
    (z, Tz) ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate →
    inner ℝ Tx z = inner ℝ x Tz) ∧
  (∀ p : ConcreteL2R2PairSpace,
    p ∈ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph ↔
      p ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier) ∧
  (∀ p : ConcreteL2R2PairSpace,
    p ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ↔
      p ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier) ∧
  True ∧ True

/-- The formal-adjoint self-adjointness precondition handoff is ready. -/
theorem concrete_l2_r2_formal_adjoint_self_adjointness_precondition_handoff_ready :
    concreteL2R2FormalAdjointSelfAdjointnessPreconditionHandoff := by
  exact ⟨
    concrete_analytic_spine_l2_r2_self_adjointness_precondition_packet_ready,
    concrete_l2_r2_formal_adjoint_closed_operator_handoff_ready,
    concrete_l2_r2_formal_adjoint_closed_operator_graph_equivalence_ready,
    concrete_l2_r2_formal_adjoint_linear_map_closed_graph_transfer_ready,
    concrete_l2_r2_formal_adjoint_linear_map_graph_symmetric,
    concrete_l2_r2_formal_adjoint_graph_candidate_symmetric,
    concrete_l2_r2_formal_adjoint_linear_map_graph_pointwise_agrees_completed_diagonal,
    concrete_l2_r2_formal_adjoint_graph_candidate_pointwise_agrees_completed_diagonal,
    trivial,
    trivial⟩

/-- Public readiness predicate for the formal-adjoint self-adjointness precondition
handoff. -/
def concreteAnalyticSpineL2R2FormalAdjointSelfAdjointnessPreconditionHandoffReady : Prop :=
  concreteL2R2FormalAdjointSelfAdjointnessPreconditionHandoff

/-- The public readiness predicate for the formal-adjoint self-adjointness
precondition handoff is ready. -/
theorem concrete_analytic_spine_l2_r2_formal_adjoint_self_adjointness_precondition_handoff_ready :
    concreteAnalyticSpineL2R2FormalAdjointSelfAdjointnessPreconditionHandoffReady := by
  exact concrete_l2_r2_formal_adjoint_self_adjointness_precondition_handoff_ready

end

end MathlibAnalytic
end MGAP4D
