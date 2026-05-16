import MGAP4D.MathlibAnalytic.Basic

namespace MGAP4D
namespace MathlibAnalytic

/-- Mathlib-backed real-valued exact-gap surface.

This is the first analytic replacement surface after the pre-Mathlib boundary:
`33/20` is represented in `ℝ`, is positive, and lies strictly above `1`. -/
structure ExactGapRealSurface where
  value : ℝ
  value_eq_3320 : value = (33 : ℝ) / 20
  positive : 0 < value
  above_one : 1 < value
  analyticReplacementBranchOnly : Prop

noncomputable def exactGapRealSurface : ExactGapRealSurface :=
  { value := exactGapValueReal
    value_eq_3320 := exactGapValueReal_eq
    positive := exactGapValueReal_pos
    above_one := by
      norm_num [exactGapValueReal]
    analyticReplacementBranchOnly := True }

def ExactGapRealSurface.ready (S : ExactGapRealSurface) : Prop :=
  S.value = (33 : ℝ) / 20 ∧ 0 < S.value ∧ 1 < S.value ∧ S.analyticReplacementBranchOnly

theorem exact_gap_real_surface_ready : exactGapRealSurface.ready := by
  exact And.intro exactGapValueReal_eq <|
    And.intro exactGapValueReal_pos <|
    And.intro (by norm_num [exactGapValueReal]) True.intro

theorem exact_gap_real_surface_value :
    exactGapRealSurface.value = (33 : ℝ) / 20 := by
  exact exactGapValueReal_eq

theorem exact_gap_real_surface_positive :
    0 < exactGapRealSurface.value := by
  exact exactGapValueReal_pos

theorem exact_gap_real_surface_above_one :
    1 < exactGapRealSurface.value := by
  norm_num [exactGapRealSurface, exactGapValueReal]

end MathlibAnalytic
end MGAP4D
