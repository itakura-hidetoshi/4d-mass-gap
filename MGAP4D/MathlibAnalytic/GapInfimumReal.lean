import MGAP4D.MathlibAnalytic.ExactGapReal

namespace MGAP4D
namespace MathlibAnalytic

/-- A Mathlib-backed real-order prototype for the exact-gap infimum surface.

The carrier is the closed upper ray above the abstract exact-gap carrier.  This
is not yet the full Hilbert-space Rayleigh quotient theorem, and it deliberately
contains no upstream `33/20` value claim. -/
noncomputable def exactGapEnergyRay : Set ℝ := Set.Ici (exactGapValueReal : ℝ)

/-- The exact gap value belongs to the analytic energy ray. -/
theorem exactGapValueReal_mem_energyRay : exactGapValueReal ∈ exactGapEnergyRay := by
  simp [exactGapEnergyRay]

/-- Every element of the analytic energy ray is bounded below by the exact gap value. -/
theorem exactGapEnergyRay_lower_bound :
    ∀ x ∈ exactGapEnergyRay, exactGapValueReal ≤ x := by
  intro x hx
  simpa [exactGapEnergyRay] using hx

/-- The exact-gap energy carrier is a closed upper real ray. -/
theorem exactGapEnergyRay_eq_closed_upper_ray :
    exactGapEnergyRay = Set.Ici exactGapValueReal := by
  rfl

/-- The exact gap value is an attained lower bound of the analytic energy ray. -/
structure GapInfimumRealSurface where
  value : ℝ
  carrier : Set ℝ
  lower_bound : ∀ x ∈ carrier, value ≤ x
  attained : value ∈ carrier
  positive : 0 < value
  carrier_closed_upper_ray : carrier = Set.Ici value

noncomputable def gapInfimumRealSurface : GapInfimumRealSurface :=
  { value := exactGapValueReal
    carrier := exactGapEnergyRay
    lower_bound := exactGapEnergyRay_lower_bound
    attained := exactGapValueReal_mem_energyRay
    positive := exactGapValueReal_pos
    carrier_closed_upper_ray := exactGapEnergyRay_eq_closed_upper_ray }

def GapInfimumRealSurface.ready (S : GapInfimumRealSurface) : Prop :=
  (∀ x ∈ S.carrier, S.value ≤ x) ∧
  S.value ∈ S.carrier ∧
  0 < S.value ∧
  S.carrier = Set.Ici S.value

theorem gap_infimum_real_surface_ready : gapInfimumRealSurface.ready := by
  exact And.intro exactGapEnergyRay_lower_bound <|
    And.intro exactGapValueReal_mem_energyRay <|
    And.intro exactGapValueReal_pos exactGapEnergyRay_eq_closed_upper_ray

theorem gap_infimum_real_surface_lower_bound :
    ∀ x ∈ gapInfimumRealSurface.carrier, gapInfimumRealSurface.value ≤ x := by
  exact exactGapEnergyRay_lower_bound

theorem gap_infimum_real_surface_attained :
    gapInfimumRealSurface.value ∈ gapInfimumRealSurface.carrier := by
  exact exactGapValueReal_mem_energyRay

theorem gap_infimum_real_surface_positive :
    0 < gapInfimumRealSurface.value := by
  exact exactGapValueReal_pos

theorem gap_infimum_real_surface_carrier_closed_upper_ray :
    gapInfimumRealSurface.carrier = Set.Ici gapInfimumRealSurface.value := by
  exact exactGapEnergyRay_eq_closed_upper_ray

end MathlibAnalytic
end MGAP4D
