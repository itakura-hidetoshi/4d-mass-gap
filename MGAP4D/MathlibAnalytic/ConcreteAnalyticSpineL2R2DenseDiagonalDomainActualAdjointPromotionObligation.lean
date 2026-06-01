import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainFormalAdjointGraphComparison

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- The dense-domain bundled diagonal map and the existing formal-adjoint graph
presentation have exactly the same graph.  This is a concrete graph identity,
not yet an invocation of Mathlib's actual adjoint predicate. -/
def concreteL2R2DenseDiagonalDomainActualAdjointGraphIdentityData : Prop :=
  concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier =
    concreteL2R2CompletedDiagonalGraphCarrier ∧
  concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier =
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier ∧
  concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier =
    concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph ∧
  IsClosed concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier ∧
  IsClosed concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph

/-- The concrete graph identity data needed before actual Mathlib-adjoint
promotion is ready. -/
theorem concrete_l2_r2_dense_diagonal_domain_actual_adjoint_graph_identity_data_ready :
    concreteL2R2DenseDiagonalDomainActualAdjointGraphIdentityData := by
  exact ⟨
    concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_completed_graph_carrier,
    by
      rw [concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_completed_graph_carrier]
      exact concrete_l2_r2_completed_diagonal_operator_graphCarrier_eq.symm,
    concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_formal_adjoint_linear_map_graph,
    concrete_l2_r2_dense_diagonal_domain_linear_map_graph_isClosed,
    concrete_l2_r2_formal_adjoint_linear_map_graph_isClosed_from_dense_diagonal_domain_graph⟩

/-- Actual-adjoint promotion obligation for the dense-domain bundled diagonal
map.

This packet is deliberately stronger than the previous handoff: it gathers the
new bundled linear map, closed graph evidence, full completed graph equality,
and formal-adjoint graph equality in one place.  It still stops before claiming
Mathlib's actual adjoint predicate or `IsSelfAdjoint`. -/
def concreteL2R2DenseDiagonalDomainActualAdjointPromotionObligation : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainFormalAdjointGraphComparisonSurfaceReady ∧
  concreteAnalyticSpineL2R2DenseDiagonalDomainClosedOperatorHandoffReady ∧
  concreteL2R2DenseDiagonalDomainActualAdjointGraphIdentityData ∧
  concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier =
    concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph ∧
  (∀ p : ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier,
    p ∈ concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier ↔
      p ∈ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph) ∧
  (∀ x : concreteL2R2DenseDiagonalDomainCarrier,
    (concreteL2R2DenseDiagonalDomainCarrierVal x,
      concreteL2R2DenseDiagonalDomainLinearMap x) ∈
        concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph)

/-- The actual-adjoint promotion obligation is ready. -/
theorem concrete_l2_r2_dense_diagonal_domain_actual_adjoint_promotion_obligation_ready :
    concreteL2R2DenseDiagonalDomainActualAdjointPromotionObligation := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_formal_adjoint_graph_comparison_surface_ready,
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_closed_operator_handoff_ready,
    concrete_l2_r2_dense_diagonal_domain_actual_adjoint_graph_identity_data_ready,
    concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_formal_adjoint_linear_map_graph,
    concrete_l2_r2_dense_diagonal_domain_linear_map_graph_mem_iff_formal_adjoint_linear_map_graph,
    concrete_l2_r2_dense_diagonal_domain_linear_map_point_mem_formal_adjoint_linear_map_graph⟩

/-- Boundary marker: all concrete graph data required before actual Mathlib
adjoint promotion is assembled, but no actual Mathlib `adjoint` or
`IsSelfAdjoint` theorem is claimed here. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainActualAdjointPromotionBoundaryHeld : Prop :=
  concreteL2R2DenseDiagonalDomainActualAdjointPromotionObligation

/-- Boundary theorem for the actual-adjoint promotion obligation. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_actual_adjoint_promotion_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainActualAdjointPromotionBoundaryHeld := by
  exact concrete_l2_r2_dense_diagonal_domain_actual_adjoint_promotion_obligation_ready

end

end MathlibAnalytic
end MGAP4D
