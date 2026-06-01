import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMap
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2InnerProductIdentification

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- Graph membership for a point of the dense-domain `LinearPMap`, transported to
the existing graph-defined completed diagonal operator carrier. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_pair_mem_completed_operator_graph
    (x : concreteL2R2DenseDiagonalDomainLinearPMap.domain) :
    ((x : ConcreteL2R1HilbertCarrier),
      concreteL2R2DenseDiagonalDomainLinearPMap x) ∈
        concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier := by
  have hxgraph :
      ((x : ConcreteL2R1HilbertCarrier),
        concreteL2R2DenseDiagonalDomainLinearPMap x) ∈
          concreteL2R2DenseDiagonalDomainLinearPMap.graph := by
    exact LinearPMap.mem_graph concreteL2R2DenseDiagonalDomainLinearPMap x
  have hxcompleted :
      ((x : ConcreteL2R1HilbertCarrier),
        concreteL2R2DenseDiagonalDomainLinearPMap x) ∈
          concreteL2R2CompletedDiagonalGraphCarrier := by
    rw [← concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_eq_completed_graph_carrier]
    exact hxgraph
  rw [concrete_l2_r2_completed_diagonal_operator_graphCarrier_eq]
  exact hxcompleted

/-- The dense-domain diagonal `LinearPMap` is a formal adjoint of itself in the
actual Mathlib `LinearPMap.IsFormalAdjoint` sense. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_isFormalAdjoint_self :
    concreteL2R2DenseDiagonalDomainLinearPMap.IsFormalAdjoint
      concreteL2R2DenseDiagonalDomainLinearPMap := by
  intro x y
  exact concrete_l2_r2_inner_product_graph_symmetry
    (concrete_l2_r2_dense_diagonal_domain_linear_pmap_pair_mem_completed_operator_graph x)
    (concrete_l2_r2_dense_diagonal_domain_linear_pmap_pair_mem_completed_operator_graph y)

/-- Since the dense-domain diagonal `LinearPMap` is a formal adjoint of itself and
its domain is dense, it is contained in its actual Mathlib adjoint. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_le_actual_adjoint :
    concreteL2R2DenseDiagonalDomainLinearPMap ≤
      LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap := by
  exact LinearPMap.IsFormalAdjoint.le_adjoint
    (T := concreteL2R2DenseDiagonalDomainLinearPMap)
    (S := concreteL2R2DenseDiagonalDomainLinearPMap)
    (hT := concrete_l2_r2_dense_diagonal_domain_linear_pmap_dense_domain)
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isFormalAdjoint_self

/-- Backwards-compatible name for the forward actual adjoint inclusion. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_le_adjoint :
    concreteL2R2DenseDiagonalDomainLinearPMap ≤
      LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap := by
  exact concrete_l2_r2_dense_diagonal_domain_linear_pmap_le_actual_adjoint

/-- Actual formal-adjoint surface for the dense-domain diagonal `LinearPMap`.
This is the first genuine Mathlib adjoint theorem layer: it proves the
`LinearPMap.IsFormalAdjoint` predicate and the inclusion into the actual adjoint.
It still stops before the reverse inclusion and hence before `IsSelfAdjoint`. -/
structure ConcreteL2R2DenseDiagonalDomainLinearPMapFormalAdjointSurface where
  linearPMapReady : concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSurfaceReady
  innerProductIdentificationReady : concreteAnalyticSpineL2R2InnerProductIdentificationReady
  isFormalAdjointSelf :
    concreteL2R2DenseDiagonalDomainLinearPMap.IsFormalAdjoint
      concreteL2R2DenseDiagonalDomainLinearPMap
  leActualAdjoint :
    concreteL2R2DenseDiagonalDomainLinearPMap ≤
      LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap
  boundaryNotReverseAdjointInclusion : Prop
  boundaryNotSelfAdjointness : Prop

/-- Concrete actual formal-adjoint surface. -/
def concreteL2R2DenseDiagonalDomainLinearPMapFormalAdjointSurface :
    ConcreteL2R2DenseDiagonalDomainLinearPMapFormalAdjointSurface :=
  { linearPMapReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_surface_ready
    innerProductIdentificationReady :=
      concrete_analytic_spine_l2_r2_inner_product_identification_ready
    isFormalAdjointSelf :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_isFormalAdjoint_self
    leActualAdjoint :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_le_actual_adjoint
    boundaryNotReverseAdjointInclusion := True
    boundaryNotSelfAdjointness := True }

/-- Readiness predicate for the actual formal-adjoint surface. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapFormalAdjointSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSurfaceReady ∧
  concreteAnalyticSpineL2R2InnerProductIdentificationReady ∧
  concreteL2R2DenseDiagonalDomainLinearPMap.IsFormalAdjoint
    concreteL2R2DenseDiagonalDomainLinearPMap ∧
  concreteL2R2DenseDiagonalDomainLinearPMap ≤
    LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap ∧
  concreteL2R2DenseDiagonalDomainLinearPMapFormalAdjointSurface.boundaryNotReverseAdjointInclusion ∧
  concreteL2R2DenseDiagonalDomainLinearPMapFormalAdjointSurface.boundaryNotSelfAdjointness

/-- The actual formal-adjoint surface is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_formal_adjoint_surface_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapFormalAdjointSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_surface_ready,
    concrete_analytic_spine_l2_r2_inner_product_identification_ready,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isFormalAdjoint_self,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_le_actual_adjoint,
    trivial,
    trivial⟩

/-- Boundary marker: the dense-domain diagonal `LinearPMap` is now a Mathlib
formal adjoint of itself and is contained in its actual adjoint.  The remaining
boundary is the reverse inclusion, equivalently actual self-adjointness. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapFormalAdjointBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapFormalAdjointSurfaceReady

/-- Boundary theorem for the actual formal-adjoint surface. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_formal_adjoint_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapFormalAdjointBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_formal_adjoint_surface_ready

end

end MathlibAnalytic
end MGAP4D