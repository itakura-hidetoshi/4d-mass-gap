import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphUnrestricted
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CompletedDiagonalOperatorClosedness

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- The bundled dense-domain linear-map graph carrier is topologically closed,
transported from the already proved closedness of the completed diagonal graph
carrier. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_map_graph_isClosed :
    IsClosed concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier := by
  rw [concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_completed_graph_carrier]
  exact concrete_l2_r2_completed_diagonal_graph_isClosed

/-- Closedness statement for the bundled dense-domain linear-map graph. -/
def concreteL2R2DenseDiagonalDomainLinearMapGraphClosed : Prop :=
  IsClosed concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier

/-- The bundled dense-domain linear-map graph is closed in the ambient Hilbert
pair space. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_map_graph_closed :
    concreteL2R2DenseDiagonalDomainLinearMapGraphClosed := by
  exact concrete_l2_r2_dense_diagonal_domain_linear_map_graph_isClosed

/-- The graph-defined completed diagonal operator closedness transfers to the
bundled dense-domain linear-map graph equality surface. -/
def concreteL2R2DenseDiagonalDomainLinearMapClosedGraphTheorem : Prop :=
  concreteL2R2DenseDiagonalDomainLinearMapGraphClosed ∧
  concreteL2R2CompletedDiagonalGraphDefinedOperatorClosed ∧
  concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier =
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier

/-- The closed graph theorem for the bundled dense-domain linear map is ready. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_map_closed_graph_theorem :
    concreteL2R2DenseDiagonalDomainLinearMapClosedGraphTheorem := by
  exact ⟨
    concrete_l2_r2_dense_diagonal_domain_linear_map_graph_closed,
    concrete_l2_r2_completed_diagonal_graph_defined_operator_closed,
    by
      rw [concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_completed_graph_carrier]
      exact concrete_l2_r2_completed_diagonal_operator_graphCarrier_eq.symm⟩

/-- Dense-domain bundled linear-map closed graph surface. -/
structure ConcreteL2R2DenseDiagonalDomainLinearMapClosedGraphSurface where
  unrestrictedGraphReady :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphUnrestrictedSurfaceReady
  completedOperatorClosednessReady :
    concreteAnalyticSpineL2R2CompletedDiagonalOperatorClosednessReady
  linearMapGraphClosed : concreteL2R2DenseDiagonalDomainLinearMapGraphClosed
  completedOperatorGraphClosed : concreteL2R2CompletedDiagonalGraphDefinedOperatorClosed
  linearMapGraphEqCompletedOperatorGraph :
    concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier =
      concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier
  boundaryNotClosedOperatorAPIInstance : Prop
  boundaryNotAdjointGraphTheorem : Prop
  boundaryNotSelfAdjointness : Prop

/-- Concrete dense-domain bundled linear-map closed graph surface. -/
def concreteL2R2DenseDiagonalDomainLinearMapClosedGraphSurface :
    ConcreteL2R2DenseDiagonalDomainLinearMapClosedGraphSurface :=
  { unrestrictedGraphReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_graph_unrestricted_surface_ready
    completedOperatorClosednessReady :=
      concrete_analytic_spine_l2_r2_completed_diagonal_operator_closedness_ready
    linearMapGraphClosed :=
      concrete_l2_r2_dense_diagonal_domain_linear_map_graph_closed
    completedOperatorGraphClosed :=
      concrete_l2_r2_completed_diagonal_graph_defined_operator_closed
    linearMapGraphEqCompletedOperatorGraph := by
      rw [concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_completed_graph_carrier]
      exact concrete_l2_r2_completed_diagonal_operator_graphCarrier_eq.symm
    boundaryNotClosedOperatorAPIInstance := True
    boundaryNotAdjointGraphTheorem := True
    boundaryNotSelfAdjointness := True }

/-- Readiness predicate for the bundled dense-domain linear-map closed graph layer. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapClosedGraphSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapGraphUnrestrictedSurfaceReady ∧
  concreteAnalyticSpineL2R2CompletedDiagonalOperatorClosednessReady ∧
  concreteL2R2DenseDiagonalDomainLinearMapGraphClosed ∧
  concreteL2R2CompletedDiagonalGraphDefinedOperatorClosed ∧
  concreteL2R2DenseDiagonalDomainLinearMapGraphCarrier =
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier ∧
  concreteL2R2DenseDiagonalDomainLinearMapClosedGraphSurface.boundaryNotClosedOperatorAPIInstance ∧
  concreteL2R2DenseDiagonalDomainLinearMapClosedGraphSurface.boundaryNotAdjointGraphTheorem ∧
  concreteL2R2DenseDiagonalDomainLinearMapClosedGraphSurface.boundaryNotSelfAdjointness

/-- The bundled dense-domain linear-map closed graph layer is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_closed_graph_surface_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapClosedGraphSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_graph_unrestricted_surface_ready,
    concrete_analytic_spine_l2_r2_completed_diagonal_operator_closedness_ready,
    concrete_l2_r2_dense_diagonal_domain_linear_map_graph_closed,
    concrete_l2_r2_completed_diagonal_graph_defined_operator_closed,
    by
      rw [concrete_l2_r2_dense_diagonal_domain_linear_map_graph_eq_completed_graph_carrier]
      exact concrete_l2_r2_completed_diagonal_operator_graphCarrier_eq.symm,
    trivial,
    trivial,
    trivial⟩

/-- Boundary marker: the bundled dense-domain linear-map graph is now closed and
identified with the existing graph-defined completed operator graph.  A future
layer still has to connect this carrier-level statement to any Mathlib
closed-operator API and then to adjoint/self-adjointness. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapClosedGraphBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapClosedGraphSurfaceReady

/-- Boundary theorem for the bundled dense-domain linear-map closed graph layer. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_closed_graph_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearMapClosedGraphBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_map_closed_graph_surface_ready

end

end MathlibAnalytic
end MGAP4D
