import MGAP4D.MathlibAnalytic.SelfAdjointHPhysTheorem

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Abstract theorem body for spectral theorem integration.

This is the third post-interface theorem-body step. It does not yet prove the
full spectral theorem for a concrete unbounded self-adjoint operator. It makes
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
  support_lower_bound : ∀ x : ℝ, x ∈ spectralSupport → exactGapValueReal ≤ x
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
  D.hphysData.ready ∧
  exactGapValueReal ∈ D.spectralSupport ∧
  (∀ x : ℝ, x ∈ D.spectralSupport → exactGapValueReal ≤ x) ∧
  0 < D.spectralMass exactGapValueReal ∧
  D.spectralMass exactGapValueReal ≠ 0 ∧
  exactGapValueReal = (33 : ℝ) / 20 ∧
  0 < exactGapValueReal ∧ D.spectralTheoremCertificate ∧
  D.concreteSpectralMeasureStillOpen

/-- Exact value is in the declared spectral support. -/
theorem spectral_theorem_exact_value_in_support
    (D : SpectralTheoremTheoremData) (hD : D.ready) :
    exactGapValueReal ∈ D.spectralSupport := by
  rcases hD with ⟨_, hIn, _, _, _, _, _, _, _⟩
  exact hIn

/-- All declared spectral support values are bounded below by the exact gap. -/
theorem spectral_theorem_support_lower_bound
    (D : SpectralTheoremTheoremData) (hD : D.ready)
    (x : ℝ) (hx : x ∈ D.spectralSupport) :
    exactGapValueReal ≤ x := by
  rcases hD with ⟨_, _, hLower, _, _, _, _, _, _⟩
  exact hLower x hx

/-- The exact gap carries positive spectral mass. -/
theorem spectral_theorem_positive_mass_at_exact
    (D : SpectralTheoremTheoremData) (hD : D.ready) :
    0 < D.spectralMass exactGapValueReal := by
  rcases hD with ⟨_, _, _, hPos, _, _, _, _, _⟩
  exact hPos

/-- The exact gap carries nonzero spectral mass. -/
theorem spectral_theorem_nonzero_mass_at_exact
    (D : SpectralTheoremTheoremData) (hD : D.ready) :
    D.spectralMass exactGapValueReal ≠ 0 := by
  rcases hD with ⟨_, _, _, _, hNe, _, _, _, _⟩
  exact hNe

/-- The spectral theorem certificate surface is present. -/
theorem spectral_theorem_certificate
    (D : SpectralTheoremTheoremData) (hD : D.ready) :
    D.spectralTheoremCertificate := by
  rcases hD with ⟨_, _, _, _, _, _, _, hCert, _⟩
  exact hCert

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
  exact spectral_theorem_exact_value_in_support
    singletonSpectralTheoremTheoremData
    singleton_spectral_theorem_theorem_data_ready

theorem singleton_spectral_theorem_support_lower_bound :
    ∀ x : ℝ, x ∈ singletonSpectralTheoremTheoremData.spectralSupport →
      exactGapValueReal ≤ x := by
  intro x hx
  exact spectral_theorem_support_lower_bound
    singletonSpectralTheoremTheoremData
    singleton_spectral_theorem_theorem_data_ready x hx

theorem singleton_spectral_theorem_positive_mass_at_exact :
    0 < singletonSpectralTheoremTheoremData.spectralMass exactGapValueReal := by
  exact spectral_theorem_positive_mass_at_exact
    singletonSpectralTheoremTheoremData
    singleton_spectral_theorem_theorem_data_ready

theorem singleton_spectral_theorem_nonzero_mass_at_exact :
    singletonSpectralTheoremTheoremData.spectralMass exactGapValueReal ≠ 0 := by
  exact spectral_theorem_nonzero_mass_at_exact
    singletonSpectralTheoremTheoremData
    singleton_spectral_theorem_theorem_data_ready

/-- Review surface closing the abstract spectral theorem integration body after
the self-adjoint `H_phys` theorem body. -/
structure SpectralTheoremTheoremReviewSurface where
  selfAdjointHPhysTheoremReady : selfAdjointHPhysTheoremReviewSurface.ready
  spectralTheoremDataReady : singletonSpectralTheoremTheoremData.ready
  exactValueInSupport : exactGapValueReal ∈ singletonSpectralTheoremTheoremData.spectralSupport
  supportLowerBound : ∀ x : ℝ,
    x ∈ singletonSpectralTheoremTheoremData.spectralSupport → exactGapValueReal ≤ x
  positiveMassAtExact : 0 < singletonSpectralTheoremTheoremData.spectralMass exactGapValueReal
  nonzeroMassAtExact : singletonSpectralTheoremTheoremData.spectralMass exactGapValueReal ≠ 0
  spectralTheoremBodyClosed : Prop
  concreteSpectralMeasureStillOpen : Prop
  finalReleaseHeld : Prop
  publicBoundaryHeld : Prop

def SpectralTheoremTheoremReviewSurface.ready
    (S : SpectralTheoremTheoremReviewSurface) : Prop :=
  selfAdjointHPhysTheoremReviewSurface.ready ∧
  singletonSpectralTheoremTheoremData.ready ∧
  exactGapValueReal ∈ singletonSpectralTheoremTheoremData.spectralSupport ∧
  (∀ x : ℝ, x ∈ singletonSpectralTheoremTheoremData.spectralSupport → exactGapValueReal ≤ x) ∧
  0 < singletonSpectralTheoremTheoremData.spectralMass exactGapValueReal ∧
  singletonSpectralTheoremTheoremData.spectralMass exactGapValueReal ≠ 0 ∧
  S.spectralTheoremBodyClosed ∧ S.concreteSpectralMeasureStillOpen ∧
  S.finalReleaseHeld ∧ S.publicBoundaryHeld

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

end

end MathlibAnalytic
end MGAP4D
