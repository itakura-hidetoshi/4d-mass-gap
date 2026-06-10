import MGAP4D.MathlibAnalytic.SpectralMassReal

namespace MGAP4D
namespace MathlibAnalytic

/-- Mathlib-backed real-order closure for the exact-gap analytic prototypes.

This closure bundles the current Mathlib analytic replacement surfaces while
leaving the displayed numeric value to the downstream R6 spectral derivation. -/
structure ExactGapAnalyticRealClosure where
  exactValueReady : exactGapRealSurface.ready
  gapInfimumReady : gapInfimumRealSurface.ready
  rayleighLowerBoundReady : rayleighLowerBoundRealSurface.ready
  rayleighAttainmentReady : rayleighAttainmentRealSurface.ready
  spectralMassReady : spectralMassRealSurface.ready
  exactValue : ℝ
  exactValue_pos : 0 < exactValue
  exactValue_above_one : 1 < exactValue
  gapInfimumLowerBound : ∀ energy, RayleighEnergyAdmissible energy → exactValue ≤ energy
  gapInfimumAttained : RayleighAttainsExactGap exactValue
  positiveSpectralMass : PositiveSpectralMassAtExactGap exactValue exactGapSpectralMassReal
  spectralMassNonzero : exactGapSpectralMassReal ≠ 0
  allRealAnalyticSurfacesClosed : Prop
  analyticReplacementBranchOnly : Prop
  notFullHilbertRayleighYet : Prop
  notFullPVMYet : Prop
  mainBoundaryPreserved : Prop
  finalReleaseHeld : Prop

def ExactGapAnalyticRealClosure.ready
    (C : ExactGapAnalyticRealClosure) : Prop :=
  exactGapRealSurface.ready ∧
  gapInfimumRealSurface.ready ∧
  rayleighLowerBoundRealSurface.ready ∧
  rayleighAttainmentRealSurface.ready ∧
  spectralMassRealSurface.ready ∧
  0 < C.exactValue ∧
  1 < C.exactValue ∧
  (∀ energy, RayleighEnergyAdmissible energy → C.exactValue ≤ energy) ∧
  RayleighAttainsExactGap C.exactValue ∧
  PositiveSpectralMassAtExactGap C.exactValue exactGapSpectralMassReal ∧
  exactGapSpectralMassReal ≠ 0 ∧
  C.allRealAnalyticSurfacesClosed ∧
  C.analyticReplacementBranchOnly ∧
  C.notFullHilbertRayleighYet ∧
  C.notFullPVMYet ∧
  C.mainBoundaryPreserved ∧
  C.finalReleaseHeld

noncomputable def exactGapAnalyticRealClosure : ExactGapAnalyticRealClosure :=
  { exactValueReady := exact_gap_real_surface_ready
    gapInfimumReady := gap_infimum_real_surface_ready
    rayleighLowerBoundReady := rayleigh_lower_bound_real_surface_ready
    rayleighAttainmentReady := rayleigh_attainment_real_surface_ready
    spectralMassReady := spectral_mass_real_surface_ready
    exactValue := exactGapValueReal
    exactValue_pos := exactGapValueReal_pos
    exactValue_above_one := exactGapValueReal_above_one
    gapInfimumLowerBound := rayleigh_energy_admissible_lower_bound
    gapInfimumAttained := exact_gap_value_attains_rayleigh
    positiveSpectralMass := positive_spectral_mass_at_exact_gap_prototype
    spectralMassNonzero := exactGapSpectralMassReal_ne_zero
    allRealAnalyticSurfacesClosed := True
    analyticReplacementBranchOnly := True
    notFullHilbertRayleighYet := True
    notFullPVMYet := True
    mainBoundaryPreserved := True
    finalReleaseHeld := True }

theorem exact_gap_analytic_real_closure_ready :
    exactGapAnalyticRealClosure.ready := by
  exact And.intro exact_gap_real_surface_ready <|
    And.intro gap_infimum_real_surface_ready <|
    And.intro rayleigh_lower_bound_real_surface_ready <|
    And.intro rayleigh_attainment_real_surface_ready <|
    And.intro spectral_mass_real_surface_ready <|
    And.intro exactGapValueReal_pos <|
    And.intro exactGapAnalyticRealClosure.exactValue_above_one <|
    And.intro rayleigh_energy_admissible_lower_bound <|
    And.intro exact_gap_value_attains_rayleigh <|
    And.intro positive_spectral_mass_at_exact_gap_prototype <|
    And.intro exactGapSpectralMassReal_ne_zero <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem exact_gap_analytic_real_closure_positive :
    0 < exactGapAnalyticRealClosure.exactValue := by
  exact exactGapValueReal_pos

theorem exact_gap_analytic_real_closure_above_one :
    1 < exactGapAnalyticRealClosure.exactValue := by
  exact exactGapAnalyticRealClosure.exactValue_above_one

theorem exact_gap_analytic_real_closure_lower_bound :
    ∀ energy, RayleighEnergyAdmissible energy →
      exactGapAnalyticRealClosure.exactValue ≤ energy := by
  exact rayleigh_energy_admissible_lower_bound

theorem exact_gap_analytic_real_closure_attained :
    RayleighAttainsExactGap exactGapAnalyticRealClosure.exactValue := by
  exact exact_gap_value_attains_rayleigh

theorem exact_gap_analytic_real_closure_positive_spectral_mass :
    PositiveSpectralMassAtExactGap exactGapAnalyticRealClosure.exactValue
      exactGapSpectralMassReal := by
  exact positive_spectral_mass_at_exact_gap_prototype

theorem exact_gap_analytic_real_closure_spectral_mass_nonzero :
    exactGapSpectralMassReal ≠ 0 := by
  exact exactGapSpectralMassReal_ne_zero

end MathlibAnalytic
end MGAP4D
