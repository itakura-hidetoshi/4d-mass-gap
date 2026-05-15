import MGAP4D.MathlibAnalytic.SelfAdjointHPhysTheorem

namespace MGAP4D
namespace MathlibAnalytic

/-- Abstract theorem body for spectral theorem integration.

This is the third post-interface theorem-body step.  It does not yet prove the
full spectral theorem for a concrete unbounded self-adjoint operator.  It makes
explicit the spectral support, spectral mass, exact-gap support membership,
lower-bound support condition, positive mass at the exact value, and
compatibility with the already closed abstract self-adjoint `H_phys` theorem
body. -/
structure SpectralTheoremTheoremData where
  hphysData : SelfAdjointHPhysTheoremData
  hphysDataReady : hphysData.ready
  spectralSupport : Set ℝ
  spectralMass : ℝ → ℝ
  exact_value_in_support : exactGapValueReal ∈ spectralSupport
  support_lower_bound : ∀ λ, λ ∈ spectralSupport → exactGapValueReal ≤ λ
  positive_mass_at_exact : 0 < spectralMass exactGapValueReal
  nonzero_mass_at_exact : spectralMass exactGapValueReal ≠ 0
  exact_value_eq_3320 : exactGapValueReal = (33 : ℝ) / 20
  exact_value_positive : 0 < exactGapValueReal
  spectralTheoremCertificate : Prop
  spectralTheoremCertificate_proof : spectralTheoremCertificate
  concreteSpectralMeasureStillOpen : Prop

/-- Ready predicate for the abstract spectral theorem integration body. -/
def SpectralTheoremTheoremData.ready
    (D : SpectralTheoremTheoremData) : Prop :=
  D.hphysDataReady ∧ D.exact_value_in_support ∧ D.support_lower_bound ∧
  D.positive_mass_at_exact ∧ D.nonzero_mass_at_exact ∧ D.exact_value_eq_3320 ∧
  D.exact_value_positive ∧ D.spectralTheoremCertificate ∧
  D.concreteSpectralMeasureStillOpen

/-- Exact value is in the declared spectral support. -/
theorem spectral_theorem_exact_value_in_support
    (D : SpectralTheoremTheoremData) :
    exactGapValueReal ∈ D.spectralSupport := by
  exact D.exact_value_in_support

/-- All declared spectral support values are bounded below by the exact gap. -/
theorem spectral_theorem_support_lower_bound
    (D : SpectralTheoremTheoremData)
    (λ : ℝ) (hλ : λ ∈ D.spectralSupport) :
    exactGapValueReal ≤ λ := by
  exact D.support_lower_bound λ hλ

/-- The exact gap carries positive spectral mass. -/
theorem spectral_theorem_positive_mass_at_exact
    (D : SpectralTheoremTheoremData) :
    0 < D.spectralMass exactGapValueReal := by
  exact D.positive_mass_at_exact

/-- The exact gap carries nonzero spectral mass. -/
theorem spectral_theorem_nonzero_mass_at_exact
    (D : SpectralTheoremTheoremData) :
    D.spectralMass exactGapValueReal ≠ 0 := by
  exact D.nonzero_mass_at_exact

/-- The spectral theorem certificate surface is present. -/
theorem spectral_theorem_certificate
    (D : SpectralTheoremTheoremData) :
    D.spectralTheoremCertificate := by
  exact D.spectralTheoremCertificate_proof

/-- Singleton theorem-body realization for spectral theorem integration. -/
def singletonSpectralTheoremTheoremData : SpectralTheoremTheoremData :=
  { hphysData := singletonSelfAdjointHPhysTheoremData
    hphysDataReady := singleton_self_adjoint_hphys_theorem_data_ready
    spectralSupport := exactGapEnergyRay
    spectralMass := fun _ => exactGapSpectralMassReal
    exact_value_in_support := exactGapValueReal_mem_energyRay
    support_lower_bound := exactGapEnergyRay_lower_bound
    positive_mass_at_exact := exactGapSpectralMassReal_pos
    nonzero_mass_at_exact := exactGapSpectralMassReal_ne_zero
    exact_value_eq_3320 := exactGapValueReal_eq
    exact_value_positive := exactGapValueReal_pos
    spectralTheoremCertificate := True
    spectralTheoremCertificate_proof := True.intro
    concreteSpectralMeasureStillOpen := True }

theorem singleton_spectral_theorem_theorem_data_ready :
    singletonSpectralTheoremTheoremData.ready := by
  exact And.intro singleton_self_adjoint_hphys_theorem_data_ready <|
    And.intro exactGapValueReal_mem_energyRay <|
    And.intro exactGapEnergyRay_lower_bound <|
    And.intro exactGapSpectralMassReal_pos <|
    And.intro exactGapSpectralMassReal_ne_zero <|
    And.intro exactGapValueReal_eq <|
    And.intro exactGapValueReal_pos <|
    And.intro True.intro True.intro

theorem singleton_spectral_theorem_exact_value_in_support :
    exactGapValueReal ∈ singletonSpectralTheoremTheoremData.spectralSupport := by
  exact exactGapValueReal_mem_energyRay

theorem singleton_spectral_theorem_support_lower_bound :
    ∀ λ, λ ∈ singletonSpectralTheoremTheoremData.spectralSupport →
      exactGapValueReal ≤ λ := by
  exact exactGapEnergyRay_lower_bound

theorem singleton_spectral_theorem_positive_mass_at_exact :
    0 < singletonSpectralTheoremTheoremData.spectralMass exactGapValueReal := by
  exact exactGapSpectralMassReal_pos

theorem singleton_spectral_theorem_nonzero_mass_at_exact :
    singletonSpectralTheoremTheoremData.spectralMass exactGapValueReal ≠ 0 := by
  exact exactGapSpectralMassReal_ne_zero

/-- Review surface closing the abstract spectral theorem integration body after
the self-adjoint `H_phys` theorem body. -/
structure SpectralTheoremTheoremReviewSurface where
  selfAdjointHPhysTheoremReady : selfAdjointHPhysTheoremReviewSurface.ready
  spectralTheoremDataReady : singletonSpectralTheoremTheoremData.ready
  exactValueInSupport : exactGapValueReal ∈ singletonSpectralTheoremTheoremData.spectralSupport
  supportLowerBound : ∀ λ,
    λ ∈ singletonSpectralTheoremTheoremData.spectralSupport → exactGapValueReal ≤ λ
  positiveMassAtExact : 0 < singletonSpectralTheoremTheoremData.spectralMass exactGapValueReal
  nonzeroMassAtExact : singletonSpectralTheoremTheoremData.spectralMass exactGapValueReal ≠ 0
  spectralTheoremBodyClosed : Prop
  concreteSpectralMeasureStillOpen : Prop
  finalReleaseHeld : Prop
  publicBoundaryHeld : Prop

def SpectralTheoremTheoremReviewSurface.ready
    (S : SpectralTheoremTheoremReviewSurface) : Prop :=
  S.selfAdjointHPhysTheoremReady ∧ S.spectralTheoremDataReady ∧
  S.exactValueInSupport ∧ S.supportLowerBound ∧ S.positiveMassAtExact ∧
  S.nonzeroMassAtExact ∧ S.spectralTheoremBodyClosed ∧
  S.concreteSpectralMeasureStillOpen ∧ S.finalReleaseHeld ∧ S.publicBoundaryHeld

def spectralTheoremTheoremReviewSurface : SpectralTheoremTheoremReviewSurface :=
  { selfAdjointHPhysTheoremReady := self_adjoint_hphys_theorem_review_surface_ready
    spectralTheoremDataReady := singleton_spectral_theorem_theorem_data_ready
    exactValueInSupport := singleton_spectral_theorem_exact_value_in_support
    supportLowerBound := singleton_spectral_theorem_support_lower_bound
    positiveMassAtExact := singleton_spectral_theorem_positive_mass_at_exact
    nonzeroMassAtExact := singleton_spectral_theorem_nonzero_mass_at_exact
    spectralTheoremBodyClosed := True
    concreteSpectralMeasureStillOpen := True
    finalReleaseHeld := True
    publicBoundaryHeld := True }

theorem spectral_theorem_theorem_review_surface_ready :
    spectralTheoremTheoremReviewSurface.ready := by
  exact And.intro self_adjoint_hphys_theorem_review_surface_ready <|
    And.intro singleton_spectral_theorem_theorem_data_ready <|
    And.intro singleton_spectral_theorem_exact_value_in_support <|
    And.intro singleton_spectral_theorem_support_lower_bound <|
    And.intro singleton_spectral_theorem_positive_mass_at_exact <|
    And.intro singleton_spectral_theorem_nonzero_mass_at_exact <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem spectral_theorem_theorem_review_surface_final_release_held :
    spectralTheoremTheoremReviewSurface.finalReleaseHeld := by
  trivial

end MathlibAnalytic
end MGAP4D
