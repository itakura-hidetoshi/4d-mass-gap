import MGAP4D.MathlibAnalytic.RayleighLowerBoundReal

namespace MGAP4D
namespace MathlibAnalytic

/-- Mathlib-backed real prototype for exact-gap attainment.

This is the real-order upper-bound/attainment companion to
`RayleighLowerBoundRealSurface`: the abstract exact-gap carrier is itself an
admissible Rayleigh-energy prototype, so the lower bound is attained. -/
def RayleighAttainsExactGap (energy : ℝ) : Prop :=
  RayleighEnergyAdmissible energy ∧ energy = exactGapValueReal

/-- The exact gap value attains the real Rayleigh lower-bound prototype. -/
theorem exact_gap_value_attains_rayleigh :
    RayleighAttainsExactGap exactGapValueReal := by
  exact And.intro exact_gap_value_rayleigh_admissible rfl

/-- There exists an admissible real Rayleigh energy attaining the exact gap. -/
theorem exists_rayleigh_exact_gap_attainment :
    ∃ energy : ℝ, RayleighAttainsExactGap energy := by
  exact ⟨exactGapValueReal, exact_gap_value_attains_rayleigh⟩

/-- Mathlib-backed real-order attainment surface for the exact-gap value. -/
structure RayleighAttainmentRealSurface where
  value : ℝ
  witnessEnergy : ℝ
  witness_admissible : RayleighEnergyAdmissible witnessEnergy
  witness_attains_value : witnessEnergy = value
  lower_bound : ∀ energy, RayleighEnergyAdmissible energy → value ≤ energy
  exists_attainment : ∃ energy : ℝ, RayleighAttainsExactGap energy
  positive : 0 < value
  analyticReplacementBranchOnly : Prop

noncomputable def rayleighAttainmentRealSurface : RayleighAttainmentRealSurface :=
  { value := exactGapValueReal
    witnessEnergy := exactGapValueReal
    witness_admissible := exact_gap_value_rayleigh_admissible
    witness_attains_value := rfl
    lower_bound := rayleigh_energy_admissible_lower_bound
    exists_attainment := exists_rayleigh_exact_gap_attainment
    positive := exactGapValueReal_pos
    analyticReplacementBranchOnly := True }

def RayleighAttainmentRealSurface.ready
    (S : RayleighAttainmentRealSurface) : Prop :=
  RayleighEnergyAdmissible S.witnessEnergy ∧
  S.witnessEnergy = S.value ∧
  (∀ energy, RayleighEnergyAdmissible energy → S.value ≤ energy) ∧
  (∃ energy : ℝ, RayleighAttainsExactGap energy) ∧
  0 < S.value ∧
  S.analyticReplacementBranchOnly

theorem rayleigh_attainment_real_surface_ready :
    rayleighAttainmentRealSurface.ready := by
  exact And.intro exact_gap_value_rayleigh_admissible <|
    And.intro rfl <|
    And.intro rayleigh_energy_admissible_lower_bound <|
    And.intro exists_rayleigh_exact_gap_attainment <|
    And.intro exactGapValueReal_pos True.intro

theorem rayleigh_attainment_real_surface_witness_admissible :
    RayleighEnergyAdmissible rayleighAttainmentRealSurface.witnessEnergy := by
  exact exact_gap_value_rayleigh_admissible

theorem rayleigh_attainment_real_surface_witness_attains_value :
    rayleighAttainmentRealSurface.witnessEnergy = rayleighAttainmentRealSurface.value := by
  rfl

theorem rayleigh_attainment_real_surface_lower_bound :
    ∀ energy, RayleighEnergyAdmissible energy →
      rayleighAttainmentRealSurface.value ≤ energy := by
  exact rayleigh_energy_admissible_lower_bound

theorem rayleigh_attainment_real_surface_exists_attainment :
    ∃ energy : ℝ, RayleighAttainsExactGap energy := by
  exact exists_rayleigh_exact_gap_attainment

theorem rayleigh_attainment_real_surface_positive :
    0 < rayleighAttainmentRealSurface.value := by
  exact exactGapValueReal_pos

end MathlibAnalytic
end MGAP4D
