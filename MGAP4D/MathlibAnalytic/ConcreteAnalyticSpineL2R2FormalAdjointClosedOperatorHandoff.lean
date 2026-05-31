import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2FormalAdjointSubmoduleLinearMap
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2ClosedOperatorTheoremObligationPacket

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Elementwise graph equivalence between the Mathlib `LinearMap` presentation of
the formal adjoint and the formal-adjoint graph candidate. -/
theorem concrete_l2_r2_formal_adjoint_linear_map_graph_mem_iff_candidate
    (p : ConcreteL2R2PairSpace) :
    p ∈ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph ↔
      p ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  rw [concrete_l2_r2_formal_adjoint_linear_map_graph_eq_candidate]

/-- Elementwise graph equivalence between the Mathlib `LinearMap` presentation of
the formal adjoint and the completed diagonal graph carrier. -/
theorem concrete_l2_r2_formal_adjoint_linear_map_graph_mem_iff_completed_diagonal_graph
    (p : ConcreteL2R2PairSpace) :
    p ∈ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph ↔
      p ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier := by
  rw [concrete_l2_r2_formal_adjoint_linear_map_graph_eq_completed_diagonal_graph]

/-- Elementwise graph equivalence between the formal-adjoint graph candidate and
the completed diagonal graph carrier. -/
theorem concrete_l2_r2_formal_adjoint_candidate_mem_iff_completed_diagonal_graph
    (p : ConcreteL2R2PairSpace) :
    p ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ↔
      p ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier := by
  constructor
  · intro hp
    have hlinear : p ∈ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph :=
      (concrete_l2_r2_formal_adjoint_linear_map_graph_mem_iff_candidate p).2 hp
    exact (concrete_l2_r2_formal_adjoint_linear_map_graph_mem_iff_completed_diagonal_graph p).1
      hlinear
  · intro hp
    have hlinear : p ∈ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph :=
      (concrete_l2_r2_formal_adjoint_linear_map_graph_mem_iff_completed_diagonal_graph p).2 hp
    exact (concrete_l2_r2_formal_adjoint_linear_map_graph_mem_iff_candidate p).1
      hlinear

/-- The Mathlib-facing formal-adjoint `LinearMap` graph is a closed graph and is
extensionally the same graph as the completed diagonal operator graph. -/
def concreteL2R2FormalAdjointClosedOperatorGraphEquivalence : Prop :=
  IsClosed concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph ∧
  IsClosed concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ∧
  IsClosed concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier ∧
  (∀ p : ConcreteL2R2PairSpace,
    p ∈ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph ↔
      p ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate) ∧
  (∀ p : ConcreteL2R2PairSpace,
    p ∈ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph ↔
      p ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier) ∧
  (∀ p : ConcreteL2R2PairSpace,
    p ∈ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate ↔
      p ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier)

/-- The formal-adjoint closed graph equivalence is fully witnessed. -/
theorem concrete_l2_r2_formal_adjoint_closed_operator_graph_equivalence_ready :
    concreteL2R2FormalAdjointClosedOperatorGraphEquivalence := by
  exact ⟨
    concrete_l2_r2_formal_adjoint_linear_map_graph_isClosed,
    concrete_l2_r2_formal_adjoint_graph_candidate_isClosed,
    concrete_l2_r2_completed_diagonal_graph_isClosed,
    concrete_l2_r2_formal_adjoint_linear_map_graph_mem_iff_candidate,
    concrete_l2_r2_formal_adjoint_linear_map_graph_mem_iff_completed_diagonal_graph,
    concrete_l2_r2_formal_adjoint_candidate_mem_iff_completed_diagonal_graph⟩

/-- Handoff from the completed diagonal closed-operator obligation packet to the
formal-adjoint `Submodule`/`LinearMap` graph presentation.

This is still not a Mathlib `adjoint` or `IsSelfAdjoint` assertion.  It records
only the concrete domain typing, chosen linear operator value, elementwise graph
equivalence, and closed graph transfer needed before such a promotion can be
made. -/
def concreteL2R2FormalAdjointClosedOperatorHandoff : Prop :=
  concreteAnalyticSpineL2R2ClosedOperatorTheoremObligationPacketReady ∧
  concreteL2R2FormalAdjointSubmoduleLinearMapTypeObligation ∧
  concreteL2R2FormalAdjointLinearMapClosedGraphTransfer ∧
  concreteL2R2FormalAdjointClosedOperatorGraphEquivalence ∧
  ((concreteL2R2CompletedDiagonalFormalAdjointDomainSubmodule :
      Set (lp (fun _ : ℕ => ℝ) 2)) =
    concreteL2R2CompletedDiagonalFormalAdjointDomainCandidate) ∧
  (∀ y : concreteL2R2CompletedDiagonalFormalAdjointDomainSubmodule,
    (y.1, concreteL2R2CompletedDiagonalFormalAdjointLinearMap y) ∈
      concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier) ∧
  (∀ y : concreteL2R2CompletedDiagonalFormalAdjointDomainSubmodule,
    (y.1, concreteL2R2CompletedDiagonalFormalAdjointLinearMap y) ∈
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate)

/-- Every point of the formal-adjoint `LinearMap` graph is also in the completed
diagonal graph carrier. -/
theorem concrete_l2_r2_formal_adjoint_linear_map_point_mem_completed_diagonal_graph
    (y : concreteL2R2CompletedDiagonalFormalAdjointDomainSubmodule) :
    (y.1, concreteL2R2CompletedDiagonalFormalAdjointLinearMap y) ∈
      concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier := by
  have hlinear :
      (y.1, concreteL2R2CompletedDiagonalFormalAdjointLinearMap y) ∈
        concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph := by
    exact ⟨y, rfl⟩
  exact
    (concrete_l2_r2_formal_adjoint_linear_map_graph_mem_iff_completed_diagonal_graph
      (y.1, concreteL2R2CompletedDiagonalFormalAdjointLinearMap y)).1 hlinear

/-- Every point of the formal-adjoint `LinearMap` graph is in the formal-adjoint
candidate graph. -/
theorem concrete_l2_r2_formal_adjoint_linear_map_point_mem_candidate
    (y : concreteL2R2CompletedDiagonalFormalAdjointDomainSubmodule) :
    (y.1, concreteL2R2CompletedDiagonalFormalAdjointLinearMap y) ∈
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  exact concrete_l2_r2_formal_adjoint_linear_map_graph_mem y

/-- The formal-adjoint closed-operator handoff is ready. -/
theorem concrete_l2_r2_formal_adjoint_closed_operator_handoff_ready :
    concreteL2R2FormalAdjointClosedOperatorHandoff := by
  exact ⟨
    concrete_analytic_spine_l2_r2_closed_operator_theorem_obligation_packet_ready,
    concrete_l2_r2_formal_adjoint_submodule_linear_map_type_obligation_ready,
    concrete_l2_r2_formal_adjoint_linear_map_closed_graph_transfer_ready,
    concrete_l2_r2_formal_adjoint_closed_operator_graph_equivalence_ready,
    concrete_l2_r2_formal_adjoint_domain_submodule_carrier_eq,
    concrete_l2_r2_formal_adjoint_linear_map_point_mem_completed_diagonal_graph,
    concrete_l2_r2_formal_adjoint_linear_map_point_mem_candidate⟩

/-- Public readiness surface for the formal-adjoint closed-operator handoff. -/
def concreteAnalyticSpineL2R2FormalAdjointClosedOperatorHandoffReady : Prop :=
  concreteL2R2FormalAdjointClosedOperatorHandoff

/-- The public readiness surface for the formal-adjoint closed-operator handoff is
ready. -/
theorem concrete_analytic_spine_l2_r2_formal_adjoint_closed_operator_handoff_ready :
    concreteAnalyticSpineL2R2FormalAdjointClosedOperatorHandoffReady := by
  exact concrete_l2_r2_formal_adjoint_closed_operator_handoff_ready

end

end MathlibAnalytic
end MGAP4D
