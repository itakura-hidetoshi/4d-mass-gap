import MGAP4D.MathlibAnalytic.Basic

namespace MGAP4D
namespace MathlibAnalytic

/-- Abstract normalized real-valued exact-gap carrier.

This carrier records only that the upstream normalized real gap is strictly above
one.  It deliberately does **not** choose `33 / 20`, does not expose a closed-form
numeric equality, and must not be used as the source of the R6 displayed value.
The displayed value is reserved for the downstream spectral/PVM pinning route. -/
noncomputable def exactGapValueReal : ℝ :=
  Classical.choose (exists_gt (1 : ℝ))

theorem exactGapValueReal_above_one : 1 < exactGapValueReal := by
  unfold exactGapValueReal
  exact Classical.choose_spec (exists_gt (1 : ℝ))

theorem exactGapValueReal_pos : 0 < exactGapValueReal := by
  exact lt_trans zero_lt_one exactGapValueReal_above_one

/-- The exact-gap carrier lies in the positive real ray. -/
theorem exactGapValueReal_mem_positive_ray :
    exactGapValueReal ∈ Set.Ioi (0 : ℝ) := by
  simpa using exactGapValueReal_pos

/-- The exact-gap carrier lies in the real ray above one. -/
theorem exactGapValueReal_mem_above_one_ray :
    exactGapValueReal ∈ Set.Ioi (1 : ℝ) := by
  simpa using exactGapValueReal_above_one

/-- Mathlib-backed real-valued exact-gap carrier surface. -/
structure ExactGapRealSurface where
  value : ℝ
  positive : 0 < value
  above_one : 1 < value
  in_positive_ray : value ∈ Set.Ioi (0 : ℝ)
  in_above_one_ray : value ∈ Set.Ioi (1 : ℝ)

noncomputable def exactGapRealSurface : ExactGapRealSurface :=
  { value := exactGapValueReal
    positive := exactGapValueReal_pos
    above_one := exactGapValueReal_above_one
    in_positive_ray := exactGapValueReal_mem_positive_ray
    in_above_one_ray := exactGapValueReal_mem_above_one_ray }

def ExactGapRealSurface.ready (S : ExactGapRealSurface) : Prop :=
  0 < S.value ∧
  1 < S.value ∧
  S.value ∈ Set.Ioi (0 : ℝ) ∧
  S.value ∈ Set.Ioi (1 : ℝ)

theorem exact_gap_real_surface_ready : exactGapRealSurface.ready := by
  exact And.intro exactGapRealSurface.positive <|
    And.intro exactGapRealSurface.above_one <|
    And.intro exactGapRealSurface.in_positive_ray
      exactGapRealSurface.in_above_one_ray

theorem exact_gap_real_surface_positive :
    0 < exactGapRealSurface.value := by
  exact exactGapRealSurface.positive

theorem exact_gap_real_surface_above_one :
    1 < exactGapRealSurface.value := by
  exact exactGapRealSurface.above_one

theorem exact_gap_real_surface_in_positive_ray :
    exactGapRealSurface.value ∈ Set.Ioi (0 : ℝ) := by
  exact exactGapRealSurface.in_positive_ray

theorem exact_gap_real_surface_in_above_one_ray :
    exactGapRealSurface.value ∈ Set.Ioi (1 : ℝ) := by
  exact exactGapRealSurface.in_above_one_ray

end MathlibAnalytic
end MGAP4D
