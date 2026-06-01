import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapFormalAdjoint
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2FormalAdjointSelfAdjointPreconditionHandoff

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- Actual Mathlib adjoint graph theorem for the dense-domain diagonal `LinearPMap`.

This is the Mathlib theorem `LinearPMap.adjoint_graph_eq_graph_adjoint`, specialized
to the concrete dense diagonal domain. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_adjoint_graph_eq_graph_adjoint :
    (LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap).graph =
      concreteL2R2DenseDiagonalDomainLinearPMap.graph.adjoint := by
  exact LinearPMap.adjoint_graph_eq_graph_adjoint
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_dense_domain

/-- The actual Mathlib adjoint of the dense-domain diagonal `LinearPMap` is closed. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_adjoint_isClosed :
    LinearPMap.IsClosed (LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap) := by
  exact LinearPMap.adjoint_isClosed
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_dense_domain

/-- Actual adjoint graph surface for the dense-domain diagonal `LinearPMap`.

This layer invokes Mathlib's actual adjoint graph theorem and adjoint closedness.
It still does not claim `T† = T`; the remaining theorem is the graph-adjoint
fixed-point statement `T.graph.adjoint = T.graph`. -/
structure ConcreteL2R2DenseDiagonalDomainLinearPMapAdjointGraphSurface where
  formalAdjointSurfaceReady :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapFormalAdjointSurfaceReady
  formalSelfAdjointPreconditionReady :
    concreteAnalyticSpineL2R2FormalAdjointSelfAdjointnessPreconditionHandoffReady
  actualAdjointGraphEqGraphAdjoint :
    (LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap).graph =
      concreteL2R2DenseDiagonalDomainLinearPMap.graph.adjoint
  actualAdjointClosed :
    LinearPMap.IsClosed (LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap)
  originalClosed :
    LinearPMap.IsClosed concreteL2R2DenseDiagonalDomainLinearPMap
  originalGraphEqCompletedGraph :
    ((concreteL2R2DenseDiagonalDomainLinearPMap.graph :
        Set (ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier)) =
      concreteL2R2CompletedDiagonalGraphCarrier)
  originalGraphEqFormalAdjointGraph :
    ((concreteL2R2DenseDiagonalDomainLinearPMap.graph :
        Set (ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier)) =
      concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph)
  boundaryNotGraphAdjointFixedPoint : Prop
  boundaryNotSelfAdjointness : Prop

/-- Concrete actual adjoint graph surface. -/
def concreteL2R2DenseDiagonalDomainLinearPMapAdjointGraphSurface :
    ConcreteL2R2DenseDiagonalDomainLinearPMapAdjointGraphSurface :=
  { formalAdjointSurfaceReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_formal_adjoint_surface_ready
    formalSelfAdjointPreconditionReady :=
      concrete_analytic_spine_l2_r2_formal_adjoint_self_adjointness_precondition_handoff_ready
    actualAdjointGraphEqGraphAdjoint :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_adjoint_graph_eq_graph_adjoint
    actualAdjointClosed :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_adjoint_isClosed
    originalClosed :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed
    originalGraphEqCompletedGraph :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_eq_completed_graph_carrier
    originalGraphEqFormalAdjointGraph :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_eq_formal_adjoint_linear_map_graph
    boundaryNotGraphAdjointFixedPoint := True
    boundaryNotSelfAdjointness := True }

/-- Readiness predicate for the actual adjoint graph surface. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapAdjointGraphSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapFormalAdjointSurfaceReady ∧
  concreteAnalyticSpineL2R2FormalAdjointSelfAdjointnessPreconditionHandoffReady ∧
  (LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap).graph =
    concreteL2R2DenseDiagonalDomainLinearPMap.graph.adjoint ∧
  LinearPMap.IsClosed (LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap) ∧
  LinearPMap.IsClosed concreteL2R2DenseDiagonalDomainLinearPMap ∧
  ((concreteL2R2DenseDiagonalDomainLinearPMap.graph :
      Set (ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier)) =
    concreteL2R2CompletedDiagonalGraphCarrier) ∧
  ((concreteL2R2DenseDiagonalDomainLinearPMap.graph :
      Set (ConcreteL2R1HilbertCarrier × ConcreteL2R1HilbertCarrier)) =
    concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph) ∧
  concreteL2R2DenseDiagonalDomainLinearPMapAdjointGraphSurface.boundaryNotGraphAdjointFixedPoint ∧
  concreteL2R2DenseDiagonalDomainLinearPMapAdjointGraphSurface.boundaryNotSelfAdjointness

/-- The actual adjoint graph surface is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_adjoint_graph_surface_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapAdjointGraphSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_formal_adjoint_surface_ready,
    concrete_analytic_spine_l2_r2_formal_adjoint_self_adjointness_precondition_handoff_ready,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_adjoint_graph_eq_graph_adjoint,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_adjoint_isClosed,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_eq_completed_graph_carrier,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_eq_formal_adjoint_linear_map_graph,
    trivial,
    trivial⟩

/-- Boundary marker: the actual adjoint graph theorem and adjoint closedness are
now available for the dense-domain diagonal `LinearPMap`.  The remaining boundary
is the graph-adjoint fixed-point theorem needed for `T† = T`. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapAdjointGraphBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapAdjointGraphSurfaceReady

/-- Boundary theorem for the actual adjoint graph surface. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_adjoint_graph_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapAdjointGraphBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_adjoint_graph_surface_ready

end

end MathlibAnalytic
end MGAP4D