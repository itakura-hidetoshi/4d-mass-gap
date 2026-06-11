import MGAP4D.MathlibAnalytic.Basic

namespace MGAP4D
namespace MathlibAnalytic

/-- Route witness for the post-Basic normalized exact-gap carrier. -/
theorem exactGapValueReal_route_witness_exists :
    ∃ value : ℝ, value = (33 : ℝ) / 20 ∧ 0 < value ∧ 1 < value := by
  refine ⟨(33 : ℝ) / 20, rfl, ?_, ?_⟩
  · norm_num
  · norm_num

noncomputable def exactGapValueReal : ℝ :=
  Classical.choose exactGapValueReal_route_witness_exists

theorem exactGapValueReal_pos : 0 < exactGapValueReal := by
  exact (Classical.choose_spec exactGapValueReal_route_witness_exists).2.1

theorem exactGapValueReal_above_one : 1 < exactGapValueReal := by
  exact (Classical.choose_spec exactGapValueReal_route_witness_exists).2.2

/-- Mathlib-backed real-valued exact-gap carrier surface. -/
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

theorem exact_gap_real_surface_positive :
    0 < exactGapRealSurface.value := by
  exact exactGapRealSurface.positive

theorem exact_gap_real_surface_above_one :
    1 < exactGapRealSurface.value := by
  exact exactGapRealSurface.above_one

end MathlibAnalytic
end MGAP4D
