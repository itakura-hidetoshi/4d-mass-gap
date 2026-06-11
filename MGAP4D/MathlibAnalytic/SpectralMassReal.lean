import MGAP4D.MathlibAnalytic.RayleighAttainmentReal

namespace MGAP4D
namespace MathlibAnalytic

/-- Mathlib-backed real prototype for a positive spectral mass at the exact gap.

This is the real-order observable-side companion to the Rayleigh lower-bound and
attainment prototypes.  It does not yet construct a projection-valued measure;
it records the positive-atom theorem body over `ℝ` without exposing an upstream
`33/20` value theorem. -/
def exactGapSpectralMassReal : ℝ := 1

/-- The prototype spectral mass at the exact gap is positive. -/
theorem exactGapSpectralMassReal_pos : 0 < exactGapSpectralMassReal := by
  norm_num [exactGapSpectralMassReal]

/-- The prototype spectral mass at the exact gap is nonzero. -/
theorem exactGapSpectralMassReal_ne_zero : exactGapSpectralMassReal ≠ 0 := by
  exact ne_of_gt exactGapSpectralMassReal_pos

/-- The prototype spectral mass is a member of the positive real ray. -/
theorem exactGapSpectralMassReal_mem_positive_ray :
    exactGapSpectralMassReal ∈ Set.Ioi (0 : ℝ) := by
  simpa using exactGapSpectralMassReal_pos

/-- A real-order positive atom at the exact gap. -/
def PositiveSpectralMassAtExactGap (value mass : ℝ) : Prop :=
  value = exactGapValueReal ∧ 0 < mass

/-- The prototype pair has positive spectral mass. -/
theorem positive_spectral_mass_at_exact_gap_prototype :
    PositiveSpectralMassAtExactGap exactGapValueReal exactGapSpectralMassReal := by
  exact And.intro rfl exactGapSpectralMassReal_pos

/-- Any positive spectral mass at the exact gap is nonzero. -/
theorem positive_spectral_mass_nonzero
    (value mass : ℝ) (h : PositiveSpectralMassAtExactGap value mass) :
    mass ≠ 0 := by
  exact ne_of_gt h.2

/-- There exists a positive real spectral mass at the exact gap prototype. -/
theorem exists_positive_spectral_mass_at_exact_gap :
    ∃ value mass : ℝ, PositiveSpectralMassAtExactGap value mass := by
  exact ⟨exactGapValueReal, exactGapSpectralMassReal,
    positive_spectral_mass_at_exact_gap_prototype⟩

/-- Mathlib-backed real positive-mass surface for the observable-side exact-gap
prototype. -/
structure SpectralMassRealSurface where
  value : ℝ
  mass : ℝ
  positive_mass : 0 < mass
  nonzero_mass : mass ≠ 0
  mass_in_positive_ray : mass ∈ Set.Ioi (0 : ℝ)
  exists_positive_mass : ∃ value mass : ℝ, PositiveSpectralMassAtExactGap value mass
  compatible_with_attainment : RayleighAttainsExactGap value

noncomputable def spectralMassRealSurface : SpectralMassRealSurface :=
  { value := exactGapValueReal
    mass := exactGapSpectralMassReal
    positive_mass := exactGapSpectralMassReal_pos
    nonzero_mass := exactGapSpectralMassReal_ne_zero
    mass_in_positive_ray := exactGapSpectralMassReal_mem_positive_ray
    exists_positive_mass := exists_positive_spectral_mass_at_exact_gap
    compatible_with_attainment := exact_gap_value_attains_rayleigh }

def SpectralMassRealSurface.ready (S : SpectralMassRealSurface) : Prop :=
  0 < S.mass ∧
  S.mass ≠ 0 ∧
  S.mass ∈ Set.Ioi (0 : ℝ) ∧
  (∃ value mass : ℝ, PositiveSpectralMassAtExactGap value mass) ∧
  RayleighAttainsExactGap S.value

theorem spectral_mass_real_surface_ready : spectralMassRealSurface.ready := by
  exact And.intro exactGapSpectralMassReal_pos <|
    And.intro exactGapSpectralMassReal_ne_zero <|
    And.intro exactGapSpectralMassReal_mem_positive_ray <|
    And.intro exists_positive_spectral_mass_at_exact_gap
      exact_gap_value_attains_rayleigh

theorem spectral_mass_real_surface_positive_mass :
    0 < spectralMassRealSurface.mass := by
  exact exactGapSpectralMassReal_pos

theorem spectral_mass_real_surface_nonzero_mass :
    spectralMassRealSurface.mass ≠ 0 := by
  exact exactGapSpectralMassReal_ne_zero

theorem spectral_mass_real_surface_mass_in_positive_ray :
    spectralMassRealSurface.mass ∈ Set.Ioi (0 : ℝ) := by
  exact exactGapSpectralMassReal_mem_positive_ray

theorem spectral_mass_real_surface_exists_positive_mass :
    ∃ value mass : ℝ, PositiveSpectralMassAtExactGap value mass := by
  exact exists_positive_spectral_mass_at_exact_gap

theorem spectral_mass_real_surface_attainment_compatible :
    RayleighAttainsExactGap spectralMassRealSurface.value := by
  exact exact_gap_value_attains_rayleigh

end MathlibAnalytic
end MGAP4D
