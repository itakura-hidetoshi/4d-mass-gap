import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPosteriorDeterminantBoundsV5_PZ37ABU
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABY — bounded slope of the unchanged posterior determinant

ABU gave the lower absolute crossing bound. Applying exp(x)>=1+x to
-the crossing in the SWAPPED exact determinant formula gives the upper
bound with exp(32*b), not the weaker exp(36*b). The determinant is exactly
k*c, with exp(-32*b)<=k<=exp(32*b). At c=0 it is zero; assigning k=1
there is only a total scalar convention, not a new density or posterior.
No continuity of this particular diagonal convention is asserted.
-/

namespace MGAP4D.MathlibAnalytic
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "cross" => p4Q2PZ37ABU_temporalCrossLog

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local instance p4Q2PZ37ABY_slope_links : Fintype Link := Fintype.ofFinite _
local notation "det" => p4Q2PZ37ABU_originalPosteriorDet H
local notation "density" => p4Q2PZ37ABT_originalPosteriorDensity H
local notation "left0" => originalWilsonExplicitIdentityBoundary H
local notation "left1" => p4Q2FQ_originalSU2LeftPiRotationAtLink H

/-- Uniform upper crossing estimate for the ORIGINAL density determinant.
The swapped positive cross product is bounded by the same FK envelope. -/
theorem p4Q2PZ37ABY_originalDet_upper_of_cross_nonneg
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) (g h : G)
    (hc : 0 ≤ cross b g h) :
    det b hb B e g h ≤ Real.exp (32 * b) * cross b g h := by
  let P : ℝ := density b hb (left1 e) B e h * density b hb left0 B e g
  have hP := p4Q2PZ37ABU_originalCrossProduct_twoSided H b hb B e h g
  have hP0 : 0 ≤ P := (Real.exp_nonneg _).trans hP.1
  have hs := p4Q2PZ37ABU_originalDet_eq_crossRatio H b hb B e h g
  rw [p4Q2PZ37ABU_originalDet_swap, p4Q2PZ37ABU_temporalCrossLog_swap] at hs
  have heq : det b hb B e g h = P * (1 - Real.exp (-cross b g h)) := by
    change -det b hb B e g h = P * (Real.exp (-cross b g h) - 1) at hs
    nlinarith
  have hlin : 1 - Real.exp (-cross b g h) ≤ cross b g h := by
    linarith [Real.add_one_le_exp (-cross b g h)]
  calc
    det b hb B e g h = P * (1 - Real.exp (-cross b g h)) := heq
    _ ≤ P * cross b g h := mul_le_mul_of_nonneg_left hlin hP0
    _ ≤ Real.exp (32 * b) * cross b g h := mul_le_mul_of_nonneg_right hP.2 hc

/-- Total exact scalar slope of the same determinant, with value one only
where the exact temporal crossing and determinant both vanish. -/
noncomputable def p4Q2PZ37ABY_originalDetSlope
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) (g h : G) : ℝ :=
  if cross b g h = 0 then 1 else det b hb B e g h / cross b g h
local notation "slope" => p4Q2PZ37ABY_originalDetSlope H

/-- The exact slope is positive and bounded uniformly in H, link and
background. No physical source or alignment premise enters this theorem. -/
theorem p4Q2PZ37ABY_originalDetSlope_twoSided
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) (g h : G) :
    Real.exp (-32 * b) ≤ slope b hb B e g h ∧
      slope b hb B e g h ≤ Real.exp (32 * b) := by
  have hRatio (x y : G) (hc : 0 < cross b x y) :
      Real.exp (-32 * b) ≤ det b hb B e x y / cross b x y ∧
        det b hb B e x y / cross b x y ≤ Real.exp (32 * b) := by
    constructor
    · exact (le_div_iff₀ hc).mpr
        (p4Q2PZ37ABU_originalDet_lower_of_cross_nonneg H b hb B e x y hc.le)
    · exact (div_le_iff₀ hc).mpr
        (p4Q2PZ37ABY_originalDet_upper_of_cross_nonneg H b hb B e x y hc.le)
  unfold p4Q2PZ37ABY_originalDetSlope
  split_ifs with hc0
  · constructor
    · simpa only [Real.exp_zero] using
        (Real.exp_le_exp.mpr (show -32 * b ≤ 0 by nlinarith))
    · simpa only [Real.exp_zero] using
        (Real.exp_le_exp.mpr (show 0 ≤ 32 * b by positivity))
  · rcases lt_or_gt_of_ne hc0 with hc | hc
    · have hcSwap : 0 < cross b h g := by
        rw [p4Q2PZ37ABU_temporalCrossLog_swap]
        exact neg_pos.mpr hc
      simpa only [p4Q2PZ37ABU_temporalCrossLog_swap,
        p4Q2PZ37ABU_originalDet_swap, neg_div_neg_eq] using hRatio h g hcSwap
    · exact hRatio g h hc

/-- Exact factorization, including the zero-crossing locus. -/
theorem p4Q2PZ37ABY_originalDet_eq_slope_mul_cross
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) (g h : G) :
    det b hb B e g h = slope b hb B e g h * cross b g h := by
  by_cases hc : cross b g h = 0
  · have hd : det b hb B e g h = 0 := by
      rw [p4Q2PZ37ABU_originalDet_eq_crossRatio, hc, Real.exp_zero]
      ring
    simp only [p4Q2PZ37ABY_originalDetSlope, hc, if_pos rfl, hd, mul_zero]
  · simp only [p4Q2PZ37ABY_originalDetSlope, if_neg hc]
    exact (div_mul_cancel₀ _ hc).symm

/-- Matching two-sided absolute bounds with no sign hypothesis. -/
theorem p4Q2PZ37ABY_originalDet_abs_twoSided
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) (g h : G) :
    Real.exp (-32 * b) * |cross b g h| ≤ |det b hb B e g h| ∧
      |det b hb B e g h| ≤ Real.exp (32 * b) * |cross b g h| := by
  have hk := p4Q2PZ37ABY_originalDetSlope_twoSided H b hb B e g h
  have hk0 : 0 ≤ slope b hb B e g h := (Real.exp_nonneg _).trans hk.1
  rw [p4Q2PZ37ABY_originalDet_eq_slope_mul_cross, abs_mul, abs_of_nonneg hk0]
  exact ⟨mul_le_mul_of_nonneg_right hk.1 (abs_nonneg _),
    mul_le_mul_of_nonneg_right hk.2 (abs_nonneg _)⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABY_originalDet_upper_of_cross_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABY_originalDetSlope_twoSided
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABY_originalDet_eq_slope_mul_cross
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABY_originalDet_abs_twoSided
