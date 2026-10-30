import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
# Signed integral error under an actual relative weight comparison

The anchor weight is retained. A positive weight does not imply a positive
signed integral: the entire absolute-value error budget remains explicit.
All integrability premises below are proved from continuity on a compact
space and the given finite measure.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
noncomputable section
set_option autoImplicit false

/-- Two relative comparisons bound the absolute error at the second value. -/
theorem abs_sub_le_mul_of_twoSidedRelativeComparison
    {a b C : ℝ} (hb : 0 ≤ b) (hC : 1 ≤ C)
    (hab : a ≤ C * b) (hba : b ≤ C * a) :
    |a - b| ≤ (C - 1) * b := by
  apply abs_le.mpr
  constructor
  · by_cases h : a ≤ b
    · have hp : 0 ≤ (C - 1) * (b - a) :=
        mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr h)
      nlinarith
    · have hba' : b ≤ a := (lt_of_not_ge h).le
      have hp : 0 ≤ (C - 1) * b := mul_nonneg (sub_nonneg.mpr hC) hb
      linarith
  · nlinarith

/-- An arbitrary signed continuous test retains its full absolute-value
budget when a positive kernel is weighted by an actual relatively bounded
continuous weight. No normalization or sign is assumed for the test. -/
theorem abs_integral_relativeWeight_sub_anchor_le
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (q w f : X → ℝ) (hq : Continuous q) (hw : Continuous w)
    (hf : Continuous f) (hq0 : ∀ x, 0 ≤ q x) (hw0 : ∀ x, 0 ≤ w x)
    (C : ℝ) (hC : 1 ≤ C) (hcompare : ∀ x y, w x ≤ C * w y) (y : X) :
    |(∫ x, q x * w x * f x ∂μ) - w y * (∫ x, q x * f x ∂μ)| ≤
      (C - 1) * w y * (∫ x, q x * |f x| ∂μ) := by
  have hc1 : Continuous (fun x => q x * w x * f x) := (hq.mul hw).mul hf
  have hc2 : Continuous (fun x => w y * (q x * f x)) :=
    continuous_const.mul (hq.mul hf)
  have hi1 : Integrable (fun x => q x * w x * f x) μ :=
    hc1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun x => w y * (q x * f x)) μ :=
    hc2.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiabs : Integrable (fun x => |q x * w x * f x - w y * (q x * f x)|) μ :=
    (hc1.sub hc2).abs.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hibound : Integrable (fun x => ((C - 1) * w y) * (q x * |f x|)) μ :=
    (continuous_const.mul (hq.mul hf.abs)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hdiff (x : X) : |w x - w y| ≤ (C - 1) * w y :=
    abs_sub_le_mul_of_twoSidedRelativeComparison (hw0 y) hC
      (hcompare x y) (hcompare y x)
  have heq : (∫ x, q x * w x * f x ∂μ) - w y * (∫ x, q x * f x ∂μ) =
      ∫ x, q x * w x * f x - w y * (q x * f x) ∂μ := by
    rw [integral_sub hi1 hi2, integral_const_mul]
  calc
    _ = |∫ x, q x * w x * f x - w y * (q x * f x) ∂μ| := congrArg abs heq
    _ ≤ ∫ x, |q x * w x * f x - w y * (q x * f x)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, ((C - 1) * w y) * (q x * |f x|) ∂μ := by
      apply integral_mono hiabs hibound
      intro x
      calc
        _ = q x * |w x - w y| * |f x| := by
          rw [show q x * w x * f x - w y * (q x * f x) =
            q x * (w x - w y) * f x by ring]
          rw [abs_mul, abs_mul, abs_of_nonneg (hq0 x)]
        _ ≤ q x * ((C - 1) * w y) * |f x| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hdiff x) (hq0 x)) (abs_nonneg _)
        _ = _ := by ring
    _ = _ := integral_const_mul _ _

/-- The corresponding signed lower estimate. Its right-hand side is not
asserted positive: a genuine positive-minus-negative margin is still needed. -/
theorem integral_relativeWeight_signed_lower
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (q w f : X → ℝ) (hq : Continuous q) (hw : Continuous w)
    (hf : Continuous f) (hq0 : ∀ x, 0 ≤ q x) (hw0 : ∀ x, 0 ≤ w x)
    (C : ℝ) (hC : 1 ≤ C) (hcompare : ∀ x y, w x ≤ C * w y) (y : X) :
    w y * ((∫ x, q x * f x ∂μ) -
      (C - 1) * (∫ x, q x * |f x| ∂μ)) ≤ ∫ x, q x * w x * f x ∂μ := by
  have h := (abs_le.mp (abs_integral_relativeWeight_sub_anchor_le
    μ q w f hq hw hf hq0 hw0 C hC hcompare y)).1
  nlinarith

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.abs_sub_le_mul_of_twoSidedRelativeComparison
#print axioms MGAP4D.MathlibAnalytic.abs_integral_relativeWeight_sub_anchor_le
#print axioms MGAP4D.MathlibAnalytic.integral_relativeWeight_signed_lower
