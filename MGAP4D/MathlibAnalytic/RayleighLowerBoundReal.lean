import MGAP4D.MathlibAnalytic.GapInfimumReal

namespace MGAP4D
namespace MathlibAnalytic

/-- Mathlib-backed real prototype for the Rayleigh lower-bound predicate.

At this stage the Hilbert-space Rayleigh quotient is represented by a real
energy value constrained to the exact-gap energy ray.  The theorem body is an
actual order-theoretic lower-bound proof over `ℝ`, with no upstream `33/20`
value claim. -/
def RayleighEnergyAdmissible (energy : ℝ) : Prop :=
  energy ∈ exactGapEnergyRay

/-- Any admissible real Rayleigh energy is bounded below by the exact gap. -/
theorem rayleigh_energy_admissible_lower_bound
    (energy : ℝ) (henergy : RayleighEnergyAdmissible energy) :
    exactGapValueReal ≤ energy := by
  exact exactGapEnergyRay_lower_bound energy henergy

/-- The exact gap value is itself an admissible Rayleigh energy prototype. -/
theorem exact_gap_value_rayleigh_admissible :
    RayleighEnergyAdmissible exactGapValueReal := by
  exact exactGapValueReal_mem_energyRay

/-- Mathlib-backed lower-bound replacement surface for the real Rayleigh prototype. -/
structure RayleighLowerBoundRealSurface where
  value : ℝ
  admissible : ℝ → Prop
  lower_bound : ∀ energy, admissible energy → value ≤ energy
  attained : admissible value
  positive : 0 < value
  analyticReplacementBranchOnly : Prop

noncomputable def rayleighLowerBoundRealSurface : RayleighLowerBoundRealSurface :=
  { value := exactGapValueReal
    admissible := RayleighEnergyAdmissible
    lower_bound := rayleigh_energy_admissible_lower_bound
    attained := exact_gap_value_rayleigh_admissible
    positive := exactGapValueReal_pos
    analyticReplacementBranchOnly := True }

def RayleighLowerBoundRealSurface.ready
    (S : RayleighLowerBoundRealSurface) : Prop :=
  (∀ energy, S.admissible energy → S.value ≤ energy) ∧
  S.admissible S.value ∧
  0 < S.value ∧
  S.analyticReplacementBranchOnly

theorem rayleigh_lower_bound_real_surface_ready :
    rayleighLowerBoundRealSurface.ready := by
  exact And.intro rayleigh_energy_admissible_lower_bound <|
    And.intro exact_gap_value_rayleigh_admissible <|
    And.intro exactGapValueReal_pos True.intro

theorem rayleigh_lower_bound_real_surface_lower_bound :
    ∀ energy, rayleighLowerBoundRealSurface.admissible energy →
      rayleighLowerBoundRealSurface.value ≤ energy := by
  exact rayleigh_energy_admissible_lower_bound

theorem rayleigh_lower_bound_real_surface_attained :
    rayleighLowerBoundRealSurface.admissible rayleighLowerBoundRealSurface.value := by
  exact exact_gap_value_rayleigh_admissible

theorem rayleigh_lower_bound_real_surface_positive :
    0 < rayleighLowerBoundRealSurface.value := by
  exact exactGapValueReal_pos

end MathlibAnalytic
end MGAP4D
