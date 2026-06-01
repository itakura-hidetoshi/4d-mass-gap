import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSelfAdjointHandoff
import MGAP4D.MathlibAnalytic.SpectralTheoremInterface

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- Spectral input handoff for the dense diagonal `LinearPMap` lane.

This layer connects the newly realized actual Mathlib self-adjointness of the
concrete dense diagonal `LinearPMap` to the existing abstract spectral review
surface.  It is an input handoff only: it does not assert the full unbounded
spectral theorem, does not construct the PVM, and does not close the positive
spectral-weight lane. -/
structure ConcreteL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffSurface where
  selfAdjointHandoffReady :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSelfAdjointHandoffReady
  spectralReviewReady :
    spectralTheoremReviewSurface.ready
  actualSelfAdjoint :
    IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap
  actualClosed :
    LinearPMap.IsClosed concreteL2R2DenseDiagonalDomainLinearPMap
  actualAdjointEqSelf :
    LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap =
      concreteL2R2DenseDiagonalDomainLinearPMap
  abstractExactValueInSupport :
    exactGapValueReal ∈ singletonSpectralTheoremInterface.spectralSupport
  abstractPositiveMass :
    0 < singletonSpectralTheoremInterface.spectralMass exactGapValueReal
  boundaryFullSpectralTheoremStillSeparate : Prop
  boundaryPVMStillSeparate : Prop
  boundaryPositiveSpectralWeightStillSeparate : Prop

/-- Concrete spectral input handoff surface. -/
def concreteL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffSurface :
    ConcreteL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffSurface :=
  { selfAdjointHandoffReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_self_adjoint_handoff_ready
    spectralReviewReady :=
      spectral_theorem_review_surface_ready
    actualSelfAdjoint :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint
    actualClosed :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed
    actualAdjointEqSelf :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self
    abstractExactValueInSupport :=
      singleton_spectral_theorem_interface_exact_in_support
    abstractPositiveMass :=
      singleton_spectral_theorem_interface_positive_mass
    boundaryFullSpectralTheoremStillSeparate := True
    boundaryPVMStillSeparate := True
    boundaryPositiveSpectralWeightStillSeparate := True }

/-- Public readiness predicate for the dense diagonal `LinearPMap` spectral input
handoff. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSelfAdjointHandoffReady ∧
  spectralTheoremReviewSurface.ready ∧
  IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap ∧
  LinearPMap.IsClosed concreteL2R2DenseDiagonalDomainLinearPMap ∧
  LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap =
    concreteL2R2DenseDiagonalDomainLinearPMap ∧
  exactGapValueReal ∈ singletonSpectralTheoremInterface.spectralSupport ∧
  0 < singletonSpectralTheoremInterface.spectralMass exactGapValueReal ∧
  concreteL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffSurface.boundaryFullSpectralTheoremStillSeparate ∧
  concreteL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffSurface.boundaryPVMStillSeparate ∧
  concreteL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffSurface.boundaryPositiveSpectralWeightStillSeparate

/-- The dense diagonal `LinearPMap` spectral input handoff is ready. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_spectral_input_handoff_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_self_adjoint_handoff_ready,
    spectral_theorem_review_surface_ready,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self,
    singleton_spectral_theorem_interface_exact_in_support,
    singleton_spectral_theorem_interface_positive_mass,
    trivial,
    trivial,
    trivial⟩

/-- Boundary marker for the spectral input handoff.

The concrete dense diagonal `LinearPMap` has crossed the actual Mathlib
self-adjointness threshold and can be used as an input to later spectral/PVM
lanes.  The spectral theorem, PVM construction, and positive spectral-weight
construction remain separate downstream obligations. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffReady

/-- The spectral input handoff boundary is held. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_spectral_input_handoff_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_spectral_input_handoff_ready

end

end MathlibAnalytic
end MGAP4D