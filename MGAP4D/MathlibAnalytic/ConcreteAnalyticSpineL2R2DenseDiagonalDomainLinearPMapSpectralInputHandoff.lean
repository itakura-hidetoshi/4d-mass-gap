import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSelfAdjointHandoff
import MGAP4D.MathlibAnalytic.SpectralTheoremInterface

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- Spectral input handoff for the dense diagonal `LinearPMap` lane.

This layer connects the newly realized actual Mathlib self-adjointness of the
concrete dense diagonal `LinearPMap` to the certified spectral review surface. -/
structure ConcreteL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffSurface where
  selfAdjointHandoffReady :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSelfAdjointHandoffReady
  spectralReviewCertified :
    spectralTheoremReviewSurface.certified
  actualSelfAdjoint :
    IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap
  actualClosed :
    LinearPMap.IsClosed concreteL2R2DenseDiagonalDomainLinearPMap
  actualAdjointEqSelf :
    LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap =
      concreteL2R2DenseDiagonalDomainLinearPMap
  abstractExactValueInSupport :
    exactGapValueReal ∈ admissibleSpectralTheoremInterface.spectralSupport
  abstractPositiveMass :
    0 < admissibleSpectralTheoremInterface.spectralMass exactGapValueReal
  spectralInterfaceCertified :
    admissibleSpectralTheoremInterface.certified
  supportEqEnergyRay :
    admissibleSpectralTheoremInterface.spectralSupport = exactGapEnergyRay
  positiveMassInPositiveRay :
    admissibleSpectralTheoremInterface.spectralMass exactGapValueReal ∈ Set.Ioi (0 : ℝ)

/-- Concrete spectral input handoff surface. -/
def concreteL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffSurface :
    ConcreteL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffSurface :=
  { selfAdjointHandoffReady :=
      concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_self_adjoint_handoff_ready
    spectralReviewCertified :=
      spectral_theorem_review_surface_certified
    actualSelfAdjoint :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint
    actualClosed :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed
    actualAdjointEqSelf :=
      concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self
    abstractExactValueInSupport :=
      admissible_spectral_theorem_interface_exact_in_support
    abstractPositiveMass :=
      admissible_spectral_theorem_interface_positive_mass
    spectralInterfaceCertified :=
      admissible_spectral_theorem_interface_certified
    supportEqEnergyRay :=
      admissible_spectral_theorem_interface_support_eq_energyRay
    positiveMassInPositiveRay :=
      admissible_spectral_theorem_interface_exact_mass_in_positive_ray }

/-- Public certification predicate for the dense diagonal `LinearPMap` spectral input
handoff. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffCertified : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSelfAdjointHandoffReady ∧
  spectralTheoremReviewSurface.certified ∧
  IsSelfAdjoint concreteL2R2DenseDiagonalDomainLinearPMap ∧
  LinearPMap.IsClosed concreteL2R2DenseDiagonalDomainLinearPMap ∧
  LinearPMap.adjoint concreteL2R2DenseDiagonalDomainLinearPMap =
    concreteL2R2DenseDiagonalDomainLinearPMap ∧
  exactGapValueReal ∈ admissibleSpectralTheoremInterface.spectralSupport ∧
  0 < admissibleSpectralTheoremInterface.spectralMass exactGapValueReal ∧
  admissibleSpectralTheoremInterface.certified ∧
  admissibleSpectralTheoremInterface.spectralSupport = exactGapEnergyRay ∧
  admissibleSpectralTheoremInterface.spectralMass exactGapValueReal ∈ Set.Ioi (0 : ℝ)

/-- Backward-compatible readiness name during downstream migration. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffReady : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffCertified

/-- The dense diagonal `LinearPMap` spectral input handoff is certified. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_spectral_input_handoff_certified :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffCertified := by
  exact ⟨
    concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_self_adjoint_handoff_ready,
    spectral_theorem_review_surface_certified,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isSelfAdjoint,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_isClosed,
    concrete_l2_r2_dense_diagonal_domain_linear_pmap_actual_adjoint_eq_self,
    admissible_spectral_theorem_interface_exact_in_support,
    admissible_spectral_theorem_interface_positive_mass,
    admissible_spectral_theorem_interface_certified,
    admissible_spectral_theorem_interface_support_eq_energyRay,
    admissible_spectral_theorem_interface_exact_mass_in_positive_ray⟩

/-- Backward-compatible theorem name during downstream migration. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_spectral_input_handoff_ready :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffReady := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_spectral_input_handoff_certified

/-- Boundary marker for the spectral input handoff. -/
def concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffCertified

/-- The spectral input handoff boundary is held. -/
theorem concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_spectral_input_handoff_boundary_held :
    concreteAnalyticSpineL2R2DenseDiagonalDomainLinearPMapSpectralInputHandoffBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_dense_diagonal_domain_linear_pmap_spectral_input_handoff_certified

end

end MathlibAnalytic
end MGAP4D