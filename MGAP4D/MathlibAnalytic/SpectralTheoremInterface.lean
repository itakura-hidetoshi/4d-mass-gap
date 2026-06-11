import MGAP4D.MathlibAnalytic.SelfAdjointHPhysInterface

namespace MGAP4D
namespace MathlibAnalytic

structure SpectralTheoremInterface where
  hphys : SelfAdjointHPhysInterface
  spectralSupport : Set ℝ
  spectralMass : ℝ → ℝ
  hphysCertified : hphys.certified
  exact_value_in_support : exactGapValueReal ∈ spectralSupport
  support_lower_bound : ∀ lam : ℝ, lam ∈ spectralSupport → exactGapValueReal ≤ lam
  positive_mass_at_exact : 0 < spectralMass exactGapValueReal
  nonzero_mass_at_exact : spectralMass exactGapValueReal ≠ 0
  support_eq_energyRay : spectralSupport = exactGapEnergyRay
  exact_mass_in_positive_ray : spectralMass exactGapValueReal ∈ Set.Ioi (0 : ℝ)

/-- Concrete certification predicate for the spectral theorem interface. -/
def SpectralTheoremInterface.certified (S : SpectralTheoremInterface) : Prop :=
  S.hphys.certified ∧
  exactGapValueReal ∈ S.spectralSupport ∧
  (∀ lam : ℝ, lam ∈ S.spectralSupport → exactGapValueReal ≤ lam) ∧
  0 < S.spectralMass exactGapValueReal ∧
  S.spectralMass exactGapValueReal ≠ 0 ∧
  S.spectralSupport = exactGapEnergyRay ∧
  S.spectralMass exactGapValueReal ∈ Set.Ioi (0 : ℝ)

/-- Backward-compatible readiness name during downstream migration. -/
def SpectralTheoremInterface.ready (S : SpectralTheoremInterface) : Prop :=
  S.certified

noncomputable def admissibleSpectralTheoremInterface : SpectralTheoremInterface :=
  { hphys := admissibleSelfAdjointHPhysInterface
    spectralSupport := exactGapEnergyRay
    spectralMass := fun _ => exactGapSpectralMassReal
    hphysCertified := admissible_self_adjoint_hphys_interface_certified
    exact_value_in_support := exactGapValueReal_mem_energyRay
    support_lower_bound := exactGapEnergyRay_lower_bound
    positive_mass_at_exact := exactGapSpectralMassReal_pos
    nonzero_mass_at_exact := exactGapSpectralMassReal_ne_zero
    support_eq_energyRay := rfl
    exact_mass_in_positive_ray := exactGapSpectralMassReal_mem_positive_ray }

theorem admissible_spectral_theorem_interface_certified :
    admissibleSpectralTheoremInterface.certified := by
  exact ⟨
    admissible_self_adjoint_hphys_interface_certified,
    exactGapValueReal_mem_energyRay,
    exactGapEnergyRay_lower_bound,
    exactGapSpectralMassReal_pos,
    exactGapSpectralMassReal_ne_zero,
    rfl,
    exactGapSpectralMassReal_mem_positive_ray⟩

/-- Backward-compatible readiness theorem during downstream migration. -/
theorem admissible_spectral_theorem_interface_ready :
    admissibleSpectralTheoremInterface.ready := by
  exact admissible_spectral_theorem_interface_certified

theorem admissible_spectral_theorem_interface_exact_in_support :
    exactGapValueReal ∈ admissibleSpectralTheoremInterface.spectralSupport := by
  exact exactGapValueReal_mem_energyRay

theorem admissible_spectral_theorem_interface_support_lower_bound :
    ∀ lam : ℝ, lam ∈ admissibleSpectralTheoremInterface.spectralSupport →
      exactGapValueReal ≤ lam := by
  exact exactGapEnergyRay_lower_bound

theorem admissible_spectral_theorem_interface_positive_mass :
    0 < admissibleSpectralTheoremInterface.spectralMass exactGapValueReal := by
  exact exactGapSpectralMassReal_pos

theorem admissible_spectral_theorem_interface_nonzero_mass :
    admissibleSpectralTheoremInterface.spectralMass exactGapValueReal ≠ 0 := by
  exact exactGapSpectralMassReal_ne_zero

theorem admissible_spectral_theorem_interface_support_eq_energyRay :
    admissibleSpectralTheoremInterface.spectralSupport = exactGapEnergyRay := by
  rfl

theorem admissible_spectral_theorem_interface_exact_mass_in_positive_ray :
    admissibleSpectralTheoremInterface.spectralMass exactGapValueReal ∈ Set.Ioi (0 : ℝ) := by
  exact exactGapSpectralMassReal_mem_positive_ray

structure SpectralTheoremReviewSurface where
  hphysReviewCertified : selfAdjointHPhysReviewSurface.certified
  spectralInterfaceCertified : admissibleSpectralTheoremInterface.certified
  exactInSupport : exactGapValueReal ∈ admissibleSpectralTheoremInterface.spectralSupport
  supportLowerBound : ∀ lam : ℝ, lam ∈ admissibleSpectralTheoremInterface.spectralSupport →
    exactGapValueReal ≤ lam
  positiveMass : 0 < admissibleSpectralTheoremInterface.spectralMass exactGapValueReal
  nonzeroMass : admissibleSpectralTheoremInterface.spectralMass exactGapValueReal ≠ 0
  support_eq_energyRay : admissibleSpectralTheoremInterface.spectralSupport = exactGapEnergyRay
  exact_mass_in_positive_ray : admissibleSpectralTheoremInterface.spectralMass exactGapValueReal ∈ Set.Ioi (0 : ℝ)

/-- Concrete certification predicate for the spectral theorem review surface. -/
def SpectralTheoremReviewSurface.certified (_S : SpectralTheoremReviewSurface) : Prop :=
  selfAdjointHPhysReviewSurface.certified ∧
  admissibleSpectralTheoremInterface.certified ∧
  exactGapValueReal ∈ admissibleSpectralTheoremInterface.spectralSupport ∧
  (∀ lam : ℝ, lam ∈ admissibleSpectralTheoremInterface.spectralSupport → exactGapValueReal ≤ lam) ∧
  0 < admissibleSpectralTheoremInterface.spectralMass exactGapValueReal ∧
  admissibleSpectralTheoremInterface.spectralMass exactGapValueReal ≠ 0 ∧
  admissibleSpectralTheoremInterface.spectralSupport = exactGapEnergyRay ∧
  admissibleSpectralTheoremInterface.spectralMass exactGapValueReal ∈ Set.Ioi (0 : ℝ)

/-- Backward-compatible readiness name during downstream migration. -/
def SpectralTheoremReviewSurface.ready (S : SpectralTheoremReviewSurface) : Prop :=
  S.certified

noncomputable def spectralTheoremReviewSurface : SpectralTheoremReviewSurface :=
  { hphysReviewCertified := self_adjoint_hphys_review_surface_certified
    spectralInterfaceCertified := admissible_spectral_theorem_interface_certified
    exactInSupport := admissible_spectral_theorem_interface_exact_in_support
    supportLowerBound := admissible_spectral_theorem_interface_support_lower_bound
    positiveMass := admissible_spectral_theorem_interface_positive_mass
    nonzeroMass := admissible_spectral_theorem_interface_nonzero_mass
    support_eq_energyRay := admissible_spectral_theorem_interface_support_eq_energyRay
    exact_mass_in_positive_ray := admissible_spectral_theorem_interface_exact_mass_in_positive_ray }

theorem spectral_theorem_review_surface_certified :
    spectralTheoremReviewSurface.certified := by
  exact ⟨
    self_adjoint_hphys_review_surface_certified,
    admissible_spectral_theorem_interface_certified,
    admissible_spectral_theorem_interface_exact_in_support,
    admissible_spectral_theorem_interface_support_lower_bound,
    admissible_spectral_theorem_interface_positive_mass,
    admissible_spectral_theorem_interface_nonzero_mass,
    admissible_spectral_theorem_interface_support_eq_energyRay,
    admissible_spectral_theorem_interface_exact_mass_in_positive_ray⟩

/-- Backward-compatible theorem name during downstream migration. -/
theorem spectral_theorem_review_surface_ready :
    spectralTheoremReviewSurface.ready := by
  exact spectral_theorem_review_surface_certified

theorem spectral_theorem_review_surface_exact_mass_in_positive_ray :
    admissibleSpectralTheoremInterface.spectralMass exactGapValueReal ∈ Set.Ioi (0 : ℝ) := by
  exact admissible_spectral_theorem_interface_exact_mass_in_positive_ray

end MathlibAnalytic
end MGAP4D