import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainClosedOperatorHandoff

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- The new dense-domain bundled linear-map graph is contained in the existing
formal-adjoint linear-map graph. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_map_graph_subset_formal_adjoint_linear_map_graph :
    concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier ⊆
      concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph := by
  intro p hp
  exact
    (concrete_l2_r2_dense_diagonal_domain_linear_map_graph_mem_iff_formal_adjoint_linear_map_graph p).1 hp

/-- The existing formal-adjoint linear-map graph is contained in the new
dense-domain bundled linear-map graph. -/
theorem concrete_l2_r2_formal_adjoint_linear_map_graph_subset_dense_diagonal_domain_linear_map_graph :
    concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph ⊆
      concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier := by
  intro p hp
  exact
    (concrete_l2_r2_dense_diagonal_domain_linear_map_graph_mem_iff_formal_adjoint_linear_map_graph p).2 hp

/-- The new dense-domain bundled linear-map graph is exactly the existing
formal-adjoint linear-map graph. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_formal_adjoint_linear_map_graph :
    concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier =
      concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph := by
  apply Set.Subset.antisymm
  · exact concrete_l2_r2_dense_diagonal_domain_linear_map_graph_subset_formal_adjoint_linear_map_graph
  · exact concrete_l2_r2_formal_adjoint_linear_map_graph_subset_dense_diagonal_domain_linear_map_graph

/-- Closedness of the existing formal-adjoint linear-map graph transported from
the new dense-domain bundled linear-map graph. -/
theorem concrete_l2_r2_formal_adjoint_linear_map_graph_isClosed_from_dense_diagonal_domain_graph :
    IsClosed concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph := by
  rw [← concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_formal_adjoint_linear_map_graph]
  exact concrete_l2_r2_dense_diagonal_domain_linear_map_graph_isClosed

/-- Formal-adjoint graph comparison surface for the new dense-domain bundled
linear map. -/
structure ConcreteL2R2DenseDiagonalDomainFormalAdjointGraphComparisonSurface where
  closedOperatorHandoffReady : concreteAnalyticSpineL2R2DenseDiagonalDomainClosedOperatorHandoffReady
  denseGraphSubsetFormalAdjointGraph :
    concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier ⊆
      concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph
  formalAdjointGraphSubsetDenseGraph :
    concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph ⊆
      concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier
  graphEqFormalAdjointGraph :
    concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier =
      concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph
  formalAdjointGraphClosed : IsClosed concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph
  boundaryNotMathlibAdjointPredicate : Prop
  boundaryNotSelfAdjointness : Prop

/-- Concrete formal-adjoint graph comparison surface. -/
def concreteL2R2DenseDiagonalDomainFormalAdjointGraphComparisonSurface :
    ConcreteL2R2DenseDiagonalDomainFormalAdjointGraphComparisonSurface :=
  { closedOperatorHandoffReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_closed_operator_handoff_ready
    denseGraphSubsetFormalAdjointGraph :=
      concrete_l2_r2_dense_diagonal_domain_linear_map_graph_subset_formal_adjoint_linear_map_graph
    formalAdjointGraphSubsetDenseGraph :=
      concrete_l2_r2_formal_adjoint_linear_map_graph_subset_dense_diagonal_domain_linear_map_graph
    graphEqFormalAdjointGraph :=
      concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_formal_adjoint_linear_map_graph
    formalAdjointGraphClosed :=
      concrete_l2_r2_formal_adjoint_linear_map_graph_isClosed_from_dense_diagonal_domain_graph
    boundaryNotMathlibAdjointPredicate := True
    boundaryNotSelfAdjointness := True }

/-- Readiness predicate for the formal-adjoint graph comparison surface. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainFormalAdjointGraphComparisonSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainClosedOperatorHandoffReady ∧
  concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier ⊆
    concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph ∧
  concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph ⊆
    concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier ∧
  concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier =
    concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph ∧
  IsClosed concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph ∧
  concreteL2R2DenseDiagonalDomainFormalAdjointGraphComparisonSurface.boundaryNotMathlibAdjointPredicate ∧
  concreteL2R2DenseDiagonalDomainFormalAdjointGraphComparisonSurface.boundaryNotSelfAdjointness

/-- The formal-adjoint graph comparison surface is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_formal_adjoint_graph_comparison_surface_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainFormalAdjointGraphComparisonSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_closed_operator_handoff_ready,
    concrete_l2_r2_dense_diagonal_domain_linear_map_graph_subset_formal_adjoint_linear_map_graph,
    concrete_l2_r2_formal_adjoint_linear_map_graph_subset_dense_diagonal_domain_linear_map_graph,
    concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_formal_adjoint_linear_map_graph,
    concrete_l2_r2_formal_adjoint_linear_map_graph_isClosed_from_dense_diagonal_domain_graph,
    trivial,
    trivial⟩

/-- Boundary marker: the new dense-domain bundled linear-map graph is now exactly
the existing formal-adjoint linear-map graph.  The remaining boundary is the
promotion from this concrete/formal graph equality to the actual Mathlib
`adjoint` predicate and then `IsSelfAdjoint`. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainFormalAdjointGraphComparisonBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainFormalAdjointGraphComparisonSurfaceReady

/-- Boundary theorem for the formal-adjoint graph comparison surface. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_formal_adjoint_graph_comparison_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainFormalAdjointGraphComparisonBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_formal_adjoint_graph_comparison_surface_ready

end

end MathlibAnalytic
end MGAP4D
