import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapFormalAdjoint

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- Domain inclusion extracted from the actual adjoint inclusion
`T ≤ LinearPMap.adjoint T`. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_domain_le_actual_adjoint_domain :
    concreteL2R2DenseDiagonalDomainLinearPMap.domain ≤
      (LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap).domain := by
  exact concrete_l2_r2_dense_diagonal_domain_linear_pmap_le_actual_adjoint.1

/-- Elementwise domain inclusion extracted from the actual adjoint inclusion. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_mem_actual_adjoint_domain_of_mem_domain
    {x : ConcreteL2R1HilbertCarrier}
    (hx : x ∈ concreteL2R2DenseDiagonalDomainLinearPMap.domain) :
    x ∈ (LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap).domain := by
  exact concrete_l2_r2_dense_diagonal_domain_linear_pmap_domain_le_actual_adjoint_domain hx

/-- On the original dense domain, the actual adjoint agrees with the original
operator.  This is only the forward inclusion consequence; it does not prove the
reverse inclusion. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_apply_eq_actual_adjoint_apply
    (x : concreteL2R2DenseDiagonalDomainLinearPMap.domain) :
    concreteL2R2DenseDiagonalDomainLinearPMap x =
      (LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap)
        ⟨(x : ConcreteL2R1HilbertCarrier),
          concrete_l2_r2_dense_diagonal_domain_linear_pmap_mem_actual_adjoint_domain_of_mem_domain
            x.2⟩ := by
  exact concrete_l2_r2_dense_diagonal_domain_linear_pmap_le_actual_adjoint.2 rfl

/-- Graph inclusion extracted from `T ≤ LinearPMap.adjoint T`. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_le_actual_adjoint_graph :
    concreteL2R2DenseDiagonalDomainLinearPMap.graph ≤
      (LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap).graph := by
  exact LinearPMap.le_graph_of_le
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_le_actual_adjoint

/-- Surface collecting the safe consequences of the forward actual adjoint
inclusion.  The reverse inclusion remains deliberately outside this layer. -/
structure ConcreteL2R2DenseDiagonalDomainLinearPMapAdjointInclusionConsequencesSurface where
  formalAdjointSurfaceReady :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapFormalAdjointSurfaceReady
  domainInclusion :
    concreteL2R2DenseDiagonalDomainLinearPMap.domain ≤
      (LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap).domain
  graphInclusion :
    concreteL2R2DenseDiagonalDomainLinearPMap.graph ≤
      (LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap).graph
  boundaryNotReverseAdjointInclusion : Prop
  boundaryNotSelfAdjointness : Prop

/-- Concrete surface for the safe consequences of the forward actual adjoint
inclusion. -/
def concreteL2R2DenseDiagonalDomainLinearPMapAdjointInclusionConsequencesSurface :
    ConcreteL2R2DenseDiagonalDomainLinearPMapAdjointInclusionConsequencesSurface :=
  { formalAdjointSurfaceReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_formal_adjoint_surface_ready
    domainInclusion :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_domain_le_actual_adjoint_domain
    graphInclusion :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_le_actual_adjoint_graph
    boundaryNotReverseAdjointInclusion := True
    boundaryNotSelfAdjointness := True }

/-- Readiness predicate for the forward actual adjoint inclusion consequences. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapAdjointInclusionConsequencesSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapFormalAdjointSurfaceReady ∧
  concreteL2R2DenseDiagonalDomainLinearPMap.domain ≤
    (LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap).domain ∧
  concreteL2R2DenseDiagonalDomainLinearPMap.graph ≤
    (LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap).graph ∧
  concreteL2R2DenseDiagonalDomainLinearPMapAdjointInclusionConsequencesSurface.boundaryNotReverseAdjointInclusion ∧
  concreteL2R2DenseDiagonalDomainLinearPMapAdjointInclusionConsequencesSurface.boundaryNotSelfAdjointness

/-- The forward actual adjoint inclusion consequences surface is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_adjoint_inclusion_consequences_surface_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapAdjointInclusionConsequencesSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_formal_adjoint_surface_ready,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_domain_le_actual_adjoint_domain,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_graph_le_actual_adjoint_graph,
    trivial,
    trivial⟩

/-- Boundary marker: the forward actual adjoint inclusion is available together
with its domain and graph consequences.  The reverse inclusion and actual
self-adjointness are still held. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapAdjointInclusionConsequencesBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapAdjointInclusionConsequencesSurfaceReady

/-- Boundary theorem for the forward actual adjoint inclusion consequences. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_adjoint_inclusion_consequences_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapAdjointInclusionConsequencesBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_adjoint_inclusion_consequences_surface_ready

end

end MathlibAnalytic
end MGAP4D