import MGAP4D.MathlibAnalytic.SpectralMassReal

namespace MGAP4D
namespace MathlibAnalytic

/-- Mathlib-backed real-order closure for the exact-gap analytic prototypes.

This closure bundles the current Mathlib analytic replacement surfaces while
leaving the displayed numeric value to the downstream R6 spectral derivation. -/
structure ExactGapAnalyticRealClosure where
  exactValueCertified : exactGapRealSurface.certified
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
  exactValue_in_positive_ray : exactValue ∈ Set.Ioi (0 : ℝ)
  exactValue_in_above_one_ray : exactValue ∈ Set.Ioi (1 : ℝ)
  exactValue_in_energyRay : exactValue ∈ exactGapEnergyRay
  gapInfimumCarrier_closed_upper_ray : gapInfimumRealSurface.carrier = Set.Ici exactValue
  spectralMass_in_positive_ray : exactGapSpectralMassReal ∈ Set.Ioi (0 : ℝ)
  rayleighWitnessAttainsExactGap : RayleighAttainsExactGap exactValue

/-- Concrete certification predicate for the analytic exact-gap closure.

The exact-value component is now certified by the Hamiltonian/PVM/spectral origin
rather than by a generic `ready` placeholder.  Older `ready` names are kept below
only as compatibility aliases to this predicate. -/
def ExactGapAnalyticRealClosure.certified
    (C : ExactGapAnalyticRealClosure) : Prop :=
  exactGapRealSurface.certified ∧
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
  C.exactValue ∈ Set.Ioi (0 : ℝ) ∧
  C.exactValue ∈ Set.Ioi (1 : ℝ) ∧
  C.exactValue ∈ exactGapEnergyRay ∧
  gapInfimumRealSurface.carrier = Set.Ici C.exactValue ∧
  exactGapSpectralMassReal ∈ Set.Ioi (0 : ℝ) ∧
  RayleighAttainsExactGap C.exactValue

/-- Backward-compatible readiness name during downstream migration. -/
def ExactGapAnalyticRealClosure.ready
    (C : ExactGapAnalyticRealClosure) : Prop :=
  C.certified

noncomputable def exactGapAnalyticRealClosure : ExactGapAnalyticRealClosure :=
  { exactValueCertified := exact_gap_real_surface_certified
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
    exactValue_in_positive_ray := exactGapValueReal_mem_positive_ray
    exactValue_in_above_one_ray := exactGapValueReal_mem_above_one_ray
    exactValue_in_energyRay := exactGapValueReal_mem_energyRay
    gapInfimumCarrier_closed_upper_ray := gap_infimum_real_surface_carrier_closed_upper_ray
    spectralMass_in_positive_ray := exactGapSpectralMassReal_mem_positive_ray
    rayleighWitnessAttainsExactGap := exact_gap_value_attains_rayleigh }

theorem exact_gap_analytic_real_closure_certified :
    exactGapAnalyticRealClosure.certified := by
  exact And.intro exact_gap_real_surface_certified <|
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
    And.intro exactGapValueReal_mem_positive_ray <|
    And.intro exactGapValueReal_mem_above_one_ray <|
    And.intro exactGapValueReal_mem_energyRay <|
    And.intro gap_infimum_real_surface_carrier_closed_upper_ray <|
    And.intro exactGapSpectralMassReal_mem_positive_ray
      exact_gap_value_attains_rayleigh

/-- Backward-compatible theorem name for downstream migration. -/
theorem exact_gap_analytic_real_closure_ready :
    exactGapAnalyticRealClosure.ready := by
  exact exact_gap_analytic_real_closure_certified

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

theorem exact_gap_analytic_real_closure_exact_value_in_positive_ray :
    exactGapAnalyticRealClosure.exactValue ∈ Set.Ioi (0 : ℝ) := by
  exact exactGapValueReal_mem_positive_ray

theorem exact_gap_analytic_real_closure_exact_value_in_energyRay :
    exactGapAnalyticRealClosure.exactValue ∈ exactGapEnergyRay := by
  exact exactGapValueReal_mem_energyRay

theorem exact_gap_analytic_real_closure_spectral_mass_in_positive_ray :
    exactGapSpectralMassReal ∈ Set.Ioi (0 : ℝ) := by
  exact exactGapSpectralMassReal_mem_positive_ray

end MathlibAnalytic
end MGAP4D