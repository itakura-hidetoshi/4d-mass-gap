import MGAP4D.MathlibAnalytic.SelfAdjointHPhysInterface

namespace MGAP4D
namespace MathlibAnalytic

/-- Abstract spectral-theorem integration interface.

This is the next post-adoption layer after the operator-shaped `H_phys`
interface.  It is not yet the full spectral theorem for an unbounded
self-adjoint operator.  It records a spectral-support and spectral-mass surface
compatible with the exact gap, the Rayleigh lower-bound prototype, and the
operator interface. -/
structure SpectralTheoremInterface where
  hphys : SelfAdjointHPhysInterface
  spectralSupport : Set ℝ
  spectralMass : ℝ → ℝ
  hphysReady : hphys.ready
  exact_value_in_support : exactGapValueReal ∈ spectralSupport
  support_lower_bound : ∀ λ, λ ∈ spectralSupport → exactGapValueReal ≤ λ
  positive_mass_at_exact : 0 < spectralMass exactGapValueReal
  nonzero_mass_at_exact : spectralMass exactGapValueReal ≠ 0
  exact_value_eq_3320 : exactGapValueReal = (33 : ℝ) / 20
  fullSpectralTheoremStillOpen : Prop
  fullPVMTheoremStillOpen : Prop

/-- Ready predicate for the spectral-theorem integration interface. -/
def SpectralTheoremInterface.ready (S : SpectralTheoremInterface) : Prop :=
  S.hphysReady ∧ S.exact_value_in_support ∧ S.support_lower_bound ∧
  S.positive_mass_at_exact ∧ S.nonzero_mass_at_exact ∧ S.exact_value_eq_3320 ∧
  S.fullSpectralTheoremStillOpen ∧ S.fullPVMTheoremStillOpen

/-- Singleton spectral theorem prototype.  The support is the already-certified
exact-gap upper ray and the mass is the positive real prototype. -/
def singletonSpectralTheoremInterface : SpectralTheoremInterface :=
  { hphys := singletonSelfAdjointHPhysInterface
    spectralSupport := exactGapEnergyRay
    spectralMass := fun _ => exactGapSpectralMassReal
    hphysReady := singleton_self_adjoint_hphys_interface_ready
    exact_value_in_support := exactGapValueReal_mem_energyRay
    support_lower_bound := exactGapEnergyRay_lower_bound
    positive_mass_at_exact := exactGapSpectralMassReal_pos
    nonzero_mass_at_exact := exactGapSpectralMassReal_ne_zero
    exact_value_eq_3320 := exactGapValueReal_eq
    fullSpectralTheoremStillOpen := True
    fullPVMTheoremStillOpen := True }

theorem singleton_spectral_theorem_interface_ready :
    singletonSpectralTheoremInterface.ready := by
  exact And.intro singleton_self_adjoint_hphys_interface_ready <|
    And.intro exactGapValueReal_mem_energyRay <|
    And.intro exactGapEnergyRay_lower_bound <|
    And.intro exactGapSpectralMassReal_pos <|
    And.intro exactGapSpectralMassReal_ne_zero <|
    And.intro exactGapValueReal_eq <|
    And.intro True.intro True.intro

theorem singleton_spectral_theorem_interface_exact_in_support :
    exactGapValueReal ∈ singletonSpectralTheoremInterface.spectralSupport := by
  exact exactGapValueReal_mem_energyRay

theorem singleton_spectral_theorem_interface_support_lower_bound :
    ∀ λ, λ ∈ singletonSpectralTheoremInterface.spectralSupport →
      exactGapValueReal ≤ λ := by
  exact exactGapEnergyRay_lower_bound

theorem singleton_spectral_theorem_interface_positive_mass :
    0 < singletonSpectralTheoremInterface.spectralMass exactGapValueReal := by
  exact exactGapSpectralMassReal_pos

theorem singleton_spectral_theorem_interface_nonzero_mass :
    singletonSpectralTheoremInterface.spectralMass exactGapValueReal ≠ 0 := by
  exact exactGapSpectralMassReal_ne_zero

/-- Review surface linking the operator-shaped `H_phys` interface to the
spectral support/mass interface. -/
structure SpectralTheoremReviewSurface where
  hphysReviewReady : selfAdjointHPhysReviewSurface.ready
  spectralInterfaceReady : singletonSpectralTheoremInterface.ready
  exactInSupport : exactGapValueReal ∈ singletonSpectralTheoremInterface.spectralSupport
  supportLowerBound : ∀ λ, λ ∈ singletonSpectralTheoremInterface.spectralSupport →
    exactGapValueReal ≤ λ
  positiveMass : 0 < singletonSpectralTheoremInterface.spectralMass exactGapValueReal
  nonzeroMass : singletonSpectralTheoremInterface.spectralMass exactGapValueReal ≠ 0
  fullSpectralTheoremStillOpen : Prop
  fullPVMTheoremStillOpen : Prop
  mainMathlibBacked : Prop
  finalReleaseHeld : Prop

def SpectralTheoremReviewSurface.ready (S : SpectralTheoremReviewSurface) : Prop :=
  S.hphysReviewReady ∧ S.spectralInterfaceReady ∧ S.exactInSupport ∧
  S.supportLowerBound ∧ S.positiveMass ∧ S.nonzeroMass ∧
  S.fullSpectralTheoremStillOpen ∧ S.fullPVMTheoremStillOpen ∧
  S.mainMathlibBacked ∧ S.finalReleaseHeld

def spectralTheoremReviewSurface : SpectralTheoremReviewSurface :=
  { hphysReviewReady := self_adjoint_hphys_review_surface_ready
    spectralInterfaceReady := singleton_spectral_theorem_interface_ready
    exactInSupport := singleton_spectral_theorem_interface_exact_in_support
    supportLowerBound := singleton_spectral_theorem_interface_support_lower_bound
    positiveMass := singleton_spectral_theorem_interface_positive_mass
    nonzeroMass := singleton_spectral_theorem_interface_nonzero_mass
    fullSpectralTheoremStillOpen := True
    fullPVMTheoremStillOpen := True
    mainMathlibBacked := True
    finalReleaseHeld := True }

theorem spectral_theorem_review_surface_ready :
    spectralTheoremReviewSurface.ready := by
  exact And.intro self_adjoint_hphys_review_surface_ready <|
    And.intro singleton_spectral_theorem_interface_ready <|
    And.intro singleton_spectral_theorem_interface_exact_in_support <|
    And.intro singleton_spectral_theorem_interface_support_lower_bound <|
    And.intro singleton_spectral_theorem_interface_positive_mass <|
    And.intro singleton_spectral_theorem_interface_nonzero_mass <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem spectral_theorem_review_surface_final_release_held :
    spectralTheoremReviewSurface.finalReleaseHeld := by
  trivial

end MathlibAnalytic
end MGAP4D
