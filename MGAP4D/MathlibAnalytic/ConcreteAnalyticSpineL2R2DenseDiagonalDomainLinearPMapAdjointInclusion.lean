import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapFormalAdjoint

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- The dense-domain diagonal `LinearPMap` is contained in its actual Mathlib
adjoint.

This uses Mathlib's `LinearPMap.IsFormalAdjoint.le_adjoint` with the dense-domain
hypothesis supplied by name, and avoids the localized postfix `†` notation so the
target remains parser-stable. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_le_actual_adjoint :
    concreteL2R2DenseDiagonalDomainLinearPMap ≤
      LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap := by
  exact LinearPMap.IsFormalAdjoint.le_adjoint
    (T := concreteL2R2DenseDiagonalDomainLinearPMap)
    (S := concreteL2R2DenseDiagonalDomainLinearPMap)
    (hT := concrete_l2_r2_dense_diagonal_domain_linear_pmap_dense_domain)
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isFormalAdjoint_self

/-- Actual adjoint inclusion surface for the dense-domain diagonal `LinearPMap`.
This is the genuine Mathlib inclusion `T ≤ T.adjoint`.  The reverse inclusion is
kept as the remaining boundary. -/
structure ConcreteL2R2DenseDiagonalDomainLinearPMapAdjointInclusionSurface where
  formalAdjointReady :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapFormalAdjointSurfaceReady
  leActualAdjoint :
    concreteL2R2DenseDiagonalDomainLinearPMap ≤
      LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap
  boundaryNotReverseAdjointInclusion : Prop
  boundaryNotSelfAdjointness : Prop

/-- Concrete actual adjoint inclusion surface. -/
def concreteL2R2DenseDiagonalDomainLinearPMapAdjointInclusionSurface :
    ConcreteL2R2DenseDiagonalDomainLinearPMapAdjointInclusionSurface :=
  { formalAdjointReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_formal_adjoint_surface_ready
    leActualAdjoint :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_le_actual_adjoint
    boundaryNotReverseAdjointInclusion := True
    boundaryNotSelfAdjointness := True }

/-- Readiness predicate for the actual adjoint inclusion surface. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapAdjointInclusionSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapFormalAdjointSurfaceReady ∧
  concreteL2R2DenseDiagonalDomainLinearPMap ≤
    LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap ∧
  concreteL2R2DenseDiagonalDomainLinearPMapAdjointInclusionSurface.boundaryNotReverseAdjointInclusion ∧
  concreteL2R2DenseDiagonalDomainLinearPMapAdjointInclusionSurface.boundaryNotSelfAdjointness

/-- The actual adjoint inclusion surface is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_adjoint_inclusion_surface_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapAdjointInclusionSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_formal_adjoint_surface_ready,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_le_actual_adjoint,
    trivial,
    trivial⟩

/-- Boundary marker: the dense-domain diagonal `LinearPMap` is now contained in
its actual Mathlib adjoint.  The reverse inclusion remains the self-adjointness
boundary. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapAdjointInclusionBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapAdjointInclusionSurfaceReady

/-- Boundary theorem for the actual adjoint inclusion surface. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_adjoint_inclusion_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapAdjointInclusionBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_adjoint_inclusion_surface_ready

end

end MathlibAnalytic
end MGAP4D
