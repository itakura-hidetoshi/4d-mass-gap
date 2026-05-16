import MGAP4D.MathlibAnalytic.ExactGapReal

namespace MGAP4D
namespace MathlibAnalytic

/-- A Mathlib-backed real-order prototype for the exact-gap infimum surface.

The carrier is the closed upper ray `[33/20, +∞)`.  This is not yet the full
Hilbert-space Rayleigh quotient theorem, but it replaces the purely structural
pre-Mathlib infimum marker by an actual `Set ℝ` lower-bound/attainment surface. -/
noncomputable def exactGapEnergyRay : Set ℝ := Set.Ici (exactGapValueReal : ℝ)

/-- The exact gap value belongs to the analytic energy ray. -/
theorem exactGapValueReal_mem_energyRay : exactGapValueReal ∈ exactGapEnergyRay := by
  simp [exactGapEnergyRay]

/-- Every element of the analytic energy ray is bounded below by the exact gap value. -/
theorem exactGapEnergyRay_lower_bound :
    ∀ x ∈ exactGapEnergyRay, exactGapValueReal ≤ x := by
  intro x hx
  simpa [exactGapEnergyRay] using hx

/-- The exact gap value is an attained lower bound of the analytic energy ray. -/
structure GapInfimumRealSurface where
  value : ℝ
  carrier : Set ℝ
  value_eq_3320 : value = (33 : ℝ) / 20
  lower_bound : ∀ x ∈ carrier, value ≤ x
  attained : value ∈ carrier
  positive : 0 < value
  analyticReplacementBranchOnly : Prop

noncomputable def gapInfimumRealSurface : GapInfimumRealSurface :=
  { value := exactGapValueReal
    carrier := exactGapEnergyRay
    value_eq_3320 := exactGapValueReal_eq
    lower_bound := exactGapEnergyRay_lower_bound
    attained := exactGapValueReal_mem_energyRay
    positive := exactGapValueReal_pos
    analyticReplacementBranchOnly := True }

def GapInfimumRealSurface.ready (S : GapInfimumRealSurface) : Prop :=
  S.value = (33 : ℝ) / 20 ∧
  (∀ x ∈ S.carrier, S.value ≤ x) ∧
  S.value ∈ S.carrier ∧
  0 < S.value ∧
  S.analyticReplacementBranchOnly

theorem gap_infimum_real_surface_ready : gapInfimumRealSurface.ready := by
  exact And.intro exactGapValueReal_eq <|
    And.intro exactGapEnergyRay_lower_bound <|
    And.intro exactGapValueReal_mem_energyRay <|
    And.intro exactGapValueReal_pos True.intro

theorem gap_infimum_real_surface_value :
    gapInfimumRealSurface.value = (33 : ℝ) / 20 := by
  exact exactGapValueReal_eq

theorem gap_infimum_real_surface_lower_bound :
    ∀ x ∈ gapInfimumRealSurface.carrier, gapInfimumRealSurface.value ≤ x := by
  exact exactGapEnergyRay_lower_bound

theorem gap_infimum_real_surface_attained :
    gapInfimumRealSurface.value ∈ gapInfimumRealSurface.carrier := by
  exact exactGapValueReal_mem_energyRay

theorem gap_infimum_real_surface_positive :
    0 < gapInfimumRealSurface.value := by
  exact exactGapValueReal_pos

end MathlibAnalytic
end MGAP4D
