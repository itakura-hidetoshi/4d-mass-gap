import MGAP4D.MathlibAnalytic.SelfAdjointHPhysInterface

namespace MGAP4D
namespace MathlibAnalytic

structure SpectralTheoremInterface where
  hphys : SelfAdjointHPhysInterface
  spectralSupport : Set ℝ
  spectralMass : ℝ → ℝ
  hphysReady : hphys.ready
  exact_value_in_support : exactGapValueReal ∈ spectralSupport
  support_lower_bound : ∀ lam : ℝ, lam ∈ spectralSupport → exactGapValueReal ≤ lam
  positive_mass_at_exact : 0 < spectralMass exactGapValueReal
  nonzero_mass_at_exact : spectralMass exactGapValueReal ≠ 0
  support_eq_energyRay : spectralSupport = exactGapEnergyRay
  exact_mass_in_positive_ray : spectralMass exactGapValueReal ∈ Set.Ioi (0 : ℝ)

def SpectralTheoremInterface.ready (S : SpectralTheoremInterface) : Prop :=
  S.hphys.ready ∧
  exactGapValueReal ∈ S.spectralSupport ∧
  (∀ lam : ℝ, lam ∈ S.spectralSupport → exactGapValueReal ≤ lam) ∧
  0 < S.spectralMass exactGapValueReal ∧
  S.spectralMass exactGapValueReal ≠ 0 ∧
  S.spectralSupport = exactGapEnergyRay ∧
  S.spectralMass exactGapValueReal ∈ Set.Ioi (0 : ℝ)

noncomputable def singletonSpectralTheoremInterface : SpectralTheoremInterface :=
  { hphys := singletonSelfAdjointHPhysInterface
    spectralSupport := exactGapEnergyRay
    spectralMass := fun _ => exactGapSpectralMassReal
    hphysReady := singleton_self_adjoint_hphys_interface_ready
    exact_value_in_support := exactGapValueReal_mem_energyRay
    support_lower_bound := exactGapEnergyRay_lower_bound
    positive_mass_at_exact := exactGapSpectralMassReal_pos
    nonzero_mass_at_exact := exactGapSpectralMassReal_ne_zero
    support_eq_energyRay := rfl
    exact_mass_in_positive_ray := exactGapSpectralMassReal_mem_positive_ray }

theorem singleton_spectral_theorem_interface_ready :
    singletonSpectralTheoremInterface.ready := by
  exact ⟨
    singleton_self_adjoint_hphys_interface_ready,
    exactGapValueReal_mem_energyRay,
    exactGapEnergyRay_lower_bound,
    exactGapSpectralMassReal_pos,
    exactGapSpectralMassReal_ne_zero,
    rfl,
    exactGapSpectralMassReal_mem_positive_ray⟩

theorem singleton_spectral_theorem_interface_exact_in_support :
    exactGapValueReal ∈ singletonSpectralTheoremInterface.spectralSupport := by
  exact exactGapValueReal_mem_energyRay

theorem singleton_spectral_theorem_interface_support_lower_bound :
    ∀ lam : ℝ, lam ∈ singletonSpectralTheoremInterface.spectralSupport →
      exactGapValueReal ≤ lam := by
  exact exactGapEnergyRay_lower_bound

theorem singleton_spectral_theorem_interface_positive_mass :
    0 < singletonSpectralTheoremInterface.spectralMass exactGapValueReal := by
  exact exactGapSpectralMassReal_pos

theorem singleton_spectral_theorem_interface_nonzero_mass :
    singletonSpectralTheoremInterface.spectralMass exactGapValueReal ≠ 0 := by
  exact exactGapSpectralMassReal_ne_zero

theorem singleton_spectral_theorem_interface_support_eq_energyRay :
    singletonSpectralTheoremInterface.spectralSupport = exactGapEnergyRay := by
  rfl

theorem singleton_spectral_theorem_interface_exact_mass_in_positive_ray :
    singletonSpectralTheoremInterface.spectralMass exactGapValueReal ∈ Set.Ioi (0 : ℝ) := by
  exact exactGapSpectralMassReal_mem_positive_ray

structure SpectralTheoremReviewSurface where
  hphysReviewReady : selfAdjointHPhysReviewSurface.ready
  spectralInterfaceReady : singletonSpectralTheoremInterface.ready
  exactInSupport : exactGapValueReal ∈ singletonSpectralTheoremInterface.spectralSupport
  supportLowerBound : ∀ lam : ℝ, lam ∈ singletonSpectralTheoremInterface.spectralSupport →
    exactGapValueReal ≤ lam
  positiveMass : 0 < singletonSpectralTheoremInterface.spectralMass exactGapValueReal
  nonzeroMass : singletonSpectralTheoremInterface.spectralMass exactGapValueReal ≠ 0
  support_eq_energyRay : singletonSpectralTheoremInterface.spectralSupport = exactGapEnergyRay
  exact_mass_in_positive_ray : singletonSpectralTheoremInterface.spectralMass exactGapValueReal ∈ Set.Ioi (0 : ℝ)

def SpectralTheoremReviewSurface.ready (_S : SpectralTheoremReviewSurface) : Prop :=
  selfAdjointHPhysReviewSurface.ready ∧
  singletonSpectralTheoremInterface.ready ∧
  exactGapValueReal ∈ singletonSpectralTheoremInterface.spectralSupport ∧
  (∀ lam : ℝ, lam ∈ singletonSpectralTheoremInterface.spectralSupport → exactGapValueReal ≤ lam) ∧
  0 < singletonSpectralTheoremInterface.spectralMass exactGapValueReal ∧
  singletonSpectralTheoremInterface.spectralMass exactGapValueReal ≠ 0 ∧
  singletonSpectralTheoremInterface.spectralSupport = exactGapEnergyRay ∧
  singletonSpectralTheoremInterface.spectralMass exactGapValueReal ∈ Set.Ioi (0 : ℝ)

noncomputable def spectralTheoremReviewSurface : SpectralTheoremReviewSurface :=
  { hphysReviewReady := self_adjoint_hphys_review_surface_ready
    spectralInterfaceReady := singleton_spectral_theorem_interface_ready
    exactInSupport := singleton_spectral_theorem_interface_exact_in_support
    supportLowerBound := singleton_spectral_theorem_interface_support_lower_bound
    positiveMass := singleton_spectral_theorem_interface_positive_mass
    nonzeroMass := singleton_spectral_theorem_interface_nonzero_mass
    support_eq_energyRay := singleton_spectral_theorem_interface_support_eq_energyRay
    exact_mass_in_positive_ray := singleton_spectral_theorem_interface_exact_mass_in_positive_ray }

theorem spectral_theorem_review_surface_ready :
    spectralTheoremReviewSurface.ready := by
  exact ⟨
    self_adjoint_hphys_review_surface_ready,
    singleton_spectral_theorem_interface_ready,
    singleton_spectral_theorem_interface_exact_in_support,
    singleton_spectral_theorem_interface_support_lower_bound,
    singleton_spectral_theorem_interface_positive_mass,
    singleton_spectral_theorem_interface_nonzero_mass,
    singleton_spectral_theorem_interface_support_eq_energyRay,
    singleton_spectral_theorem_interface_exact_mass_in_positive_ray⟩

theorem spectral_theorem_review_surface_exact_mass_in_positive_ray :
    singletonSpectralTheoremInterface.spectralMass exactGapValueReal ∈ Set.Ioi (0 : ℝ) := by
  exact singleton_spectral_theorem_interface_exact_mass_in_positive_ray

end MathlibAnalytic
end MGAP4D
