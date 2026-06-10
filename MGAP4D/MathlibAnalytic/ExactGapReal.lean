import MGAP4D.MathlibAnalytic.Basic

namespace MGAP4D
namespace MathlibAnalytic

/-- Mathlib-backed real-valued exact-gap carrier surface.

This is the first analytic replacement surface after the pre-Mathlib boundary.
It records a concrete real carrier, positivity, and the above-one lower scale, but
it no longer exposes `value = 33/20`.  The displayed exact value is first exported
at the R6 spectral derivation surface. -/
structure ExactGapRealSurface where
  value : ℝ
  positive : 0 < value
  above_one : 1 < value
  analyticReplacementBranchOnly : Prop

noncomputable def exactGapRealSurface : ExactGapRealSurface :=
  { value := exactGapValueReal
    positive := exactGapValueReal_pos
    above_one := exactGapValueReal_above_one
    analyticReplacementBranchOnly := True }

def ExactGapRealSurface.ready (S : ExactGapRealSurface) : Prop :=
  0 < S.value ∧ 1 < S.value ∧ S.analyticReplacementBranchOnly

theorem exact_gap_real_surface_ready : exactGapRealSurface.ready := by
  exact And.intro exactGapRealSurface.positive <|
    And.intro exactGapRealSurface.above_one True.intro

/-- Arithmetic positivity projection for the normalized carrier surface. -/
theorem exact_gap_real_surface_positive :
    0 < exactGapRealSurface.value := by
  exact exactGapRealSurface.positive

/-- Arithmetic above-one projection for the normalized carrier surface. -/
theorem exact_gap_real_surface_above_one :
    1 < exactGapRealSurface.value := by
  exact exactGapRealSurface.above_one

end MathlibAnalytic
end MGAP4D
