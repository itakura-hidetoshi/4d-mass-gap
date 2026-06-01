import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapClosedGraph
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2FormalAdjointClosedOperatorHandoff

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- Elementwise graph equivalence between the new dense-domain bundled linear-map
graph and the existing completed diagonal graph carrier. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_map_graph_mem_iff_completed_graph_carrier
    (p : ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier) :
    p ∈ concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier ↔
      p ∈ concreteL2R2CompletedDiagonalGraphCarrier := by
  rw [concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_completed_graph_carrier]

/-- Elementwise graph equivalence between the new dense-domain bundled linear-map
graph and the graph-defined completed diagonal operator carrier. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_map_graph_mem_iff_completed_operator_graph
    (p : ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier) :
    p ∈ concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier ↔
      p ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier := by
  rw [concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_completed_graph_carrier]
  rw [concrete_l2_r2_completed_diagonal_operator_graphCarrier_eq]

/-- Elementwise graph equivalence between the new dense-domain bundled linear-map
graph and the formal-adjoint linear-map graph. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_map_graph_mem_iff_formal_adjoint_linear_map_graph
    (p : ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier) :
    p ∈ concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier ↔
      p ∈ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph := by
  rw [concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_completed_graph_carrier]
  rw [← concrete_l2_r2_formal_adjoint_linear_map_graph_eq_completed_diagonal_graph]
  rw [concrete_l2_r2_completed_diagonal_operator_graphCarrier_eq]

/-- Closed-operator-style graph equivalence for the new dense-domain bundled
linear map. -/
def concreteL2R2DenseDiagonalDomainClosedOperatorGraphEquivalence : Prop :=
  IsClosed concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier ∧
  IsClosed concreteL2R2CompletedDiagonalGraphCarrier ∧
  IsClosed concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier ∧
  (∀ p : ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier,
    p ∈ concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier ↔
      p ∈ concreteL2R2CompletedDiagonalGraphCarrier) ∧
  (∀ p : ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier,
    p ∈ concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier ↔
      p ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier) ∧
  (∀ p : ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier,
    p ∈ concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier ↔
      p ∈ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph)

/-- The dense-domain closed-operator-style graph equivalence is ready. -/
theorem concrete_l2_r2_dense_diagonal_domain_closed_operator_graph_equivalence_ready :
    concreteL2R2DenseDiagonalDomainClosedOperatorGraphEquivalence := by
  exact ⟨
    concrete_l2_r2_dense_diagonal_domain_linear_map_graph_isClosed,
    concrete_l2_r2_completed_diagonal_graph_isClosed,
    concrete_l2_r2_completed_diagonal_operator_graph_isClosed,
    concrete_l2_r2_dense_diagonal_domain_linear_map_graph_mem_iff_completed_graph_carrier,
    concrete_l2_r2_dense_diagonal_domain_linear_map_graph_mem_iff_completed_operator_graph,
    concrete_l2_r2_dense_diagonal_domain_linear_map_graph_mem_iff_formal_adjoint_linear_map_graph⟩

/-- Every point of the new dense-domain bundled linear-map graph is in the
completed diagonal operator graph carrier. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_map_point_mem_completed_operator_graph
    (x : concreteL2R2DenseDiagonalDomainCarrier) :
    (concreteL2R2DenseDiagonalDomainCarrierVal x,
      concreteL2R2DenseDiagonalDomainLinearMap x) ∈
        concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier := by
  exact
    (concrete_l2_r2_dense_diagonal_domain_linear_map_graph_mem_iff_completed_operator_graph
      (concreteL2R2DenseDiagonalDomainCarrierVal x,
        concreteL2R2DenseDiagonalDomainLinearMap x)).1
      ⟨x, rfl, rfl⟩

/-- Every point of the new dense-domain bundled linear-map graph is in the
formal-adjoint linear-map graph. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_map_point_mem_formal_adjoint_linear_map_graph
    (x : concreteL2R2DenseDiagonalDomainCarrier) :
    (concreteL2R2DenseDiagonalDomainCarrierVal x,
      concreteL2R2DenseDiagonalDomainLinearMap x) ∈
        concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph := by
  exact
    (concrete_l2_r2_dense_diagonal_domain_linear_map_graph_mem_iff_formal_adjoint_linear_map_graph
      (concreteL2R2DenseDiagonalDomainCarrierVal x,
        concreteL2R2DenseDiagonalDomainLinearMap x)).1
      ⟨x, rfl, rfl⟩

/-- Closed-operator handoff for the new dense-domain bundled linear map.

This records that the new linear-map graph is closed and is the same graph as the
completed diagonal graph, the graph-defined completed operator, and the existing
formal-adjoint linear-map graph.  It is still not a Mathlib `adjoint` or
`IsSelfAdjoint` assertion. -/
def concreteL2R2DenseDiagonalDomainClosedOperatorHandoff : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapClosedGraphSurfaceReady ∧
  concreteAnalyticSpineL2R2FormalAdjointClosedOperatorHandoffReady ∧
  concreteL2R2DenseDiagonalDomainClosedOperatorGraphEquivalence ∧
  (∀ x : concreteL2R2DenseDiagonalDomainCarrier,
    (concreteL2R2DenseDiagonalDomainCarrierVal x,
      concreteL2R2DenseDiagonalDomainLinearMap x) ∈
        concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier) ∧
  (∀ x : concreteL2R2DenseDiagonalDomainCarrier,
    (concreteL2R2DenseDiagonalDomainCarrierVal x,
      concreteL2R2DenseDiagonalDomainLinearMap x) ∈
        concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph)

/-- The dense-domain closed-operator handoff is ready. -/
theorem concrete_l2_r2_dense_diagonal_domain_closed_operator_handoff_ready :
    concreteL2R2DenseDiagonalDomainClosedOperatorHandoff := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_closed_graph_surface_ready,
    concrete_analytic_spine_l2_r2_formal_adjoint_closed_operator_handoff_ready,
    concrete_l2_r2_dense_diagonal_domain_closed_operator_graph_equivalence_ready,
    concrete_l2_r2_dense_diagonal_domain_linear_map_point_mem_completed_operator_graph,
    concrete_l2_r2_dense_diagonal_domain_linear_map_point_mem_formal_adjoint_linear_map_graph⟩

/-- Public readiness surface for the new dense-domain closed-operator handoff. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainClosedOperatorHandoffReady : Prop :=
  concreteL2R2DenseDiagonalDomainClosedOperatorHandoff

/-- The public readiness surface for the new dense-domain closed-operator handoff
is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_closed_operator_handoff_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainClosedOperatorHandoffReady := by
  exact concrete_l2_r2_dense_diagonal_domain_closed_operator_handoff_ready

end

end MathlibAnalytic
end MGAP4D
