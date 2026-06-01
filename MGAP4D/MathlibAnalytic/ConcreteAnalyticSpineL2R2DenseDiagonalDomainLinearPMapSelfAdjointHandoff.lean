import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSelfAdjoint

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- Closedness recovered from the actual Mathlib self-adjointness theorem.

The closedness theorem already exists directly for the dense diagonal `LinearPMap`;
this result records the independent Mathlib consequence of `IsSelfAdjoint`. -/
theorem concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed_from_isSelfAdjoint :
    LinearPMap.IsClosed concreteL2R2DenseDiagonalDomainLinearPMap := by
  exact IsSelfAdjoint.isClosed
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint

/-- The dense diagonal `LinearPMap` has the post-adjoint-promotion analytic spine
package needed by later spectral/PVM lanes: dense domain, closed graph, actual
adjoint equality, and actual Mathlib self-adjointness. -/
structure ConcreteL2R2DenseDiagonalDomainLinearPMapSelfAdjointHandoffSurface where
  selfAdjointSurfaceReady :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSelfAdjointSurfaceReady
  denseDomain :
    Dense ((concreteL2R2DenseDiagonalDomainLinearPMap.domain :
      Set ConcreteL2R1HilbertCarrier))
  originalClosed :
    LinearPMap.IsClosed concreteL2R2DenseDiagonalDomainLinearPMap
  closedFromSelfAdjoint :
    LinearPMap.IsClosed concreteL2R2DenseDiagonalDomainLinearPMap
  actualAdjointEqSelf :
    LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap =
      concreteL2R2DenseDiagonalDomainLinearPMap
  isSelfAdjoint :
    IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap

/-- Concrete post-adjoint-promotion handoff surface. -/
def concreteL2R2DenseDiagonalDomainLinearPMapSelfAdjointHandoffSurface :
    ConcreteL2R2DenseDiagonalDomainLinearPMapSelfAdjointHandoffSurface :=
  { selfAdjointSurfaceReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_self_adjoint_surface_ready
    denseDomain :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_dense_domain
    originalClosed :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed
    closedFromSelfAdjoint :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed_from_isSelfAdjoint
    actualAdjointEqSelf :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self
    isSelfAdjoint :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint }

/-- Public readiness predicate for the post-adjoint-promotion handoff. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSelfAdjointHandoffReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSelfAdjointSurfaceReady ∧
  Dense ((concreteL2R2DenseDiagonalDomainLinearPMap.domain :
    Set ConcreteL2R1HilbertCarrier)) ∧
  LinearPMap.IsClosed concreteL2R2DenseDiagonalDomainLinearPMap ∧
  LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap =
    concreteL2R2DenseDiagonalDomainLinearPMap ∧
  IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap

/-- The post-adjoint-promotion handoff is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_self_adjoint_handoff_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSelfAdjointHandoffReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_self_adjoint_surface_ready,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_dense_domain,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint⟩

/-- Boundary marker for the realized self-adjointness handoff.

This closes the former actual-adjoint/self-adjointness obstruction for the dense
diagonal `LinearPMap` lane, while leaving spectral theorem, PVM construction, and
positive spectral weight as separate later lanes. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSelfAdjointHandoffBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSelfAdjointHandoffReady

/-- The realized self-adjointness handoff boundary is held. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_self_adjoint_handoff_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSelfAdjointHandoffBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_self_adjoint_handoff_ready

end

end MathlibAnalytic
end MGAP4D