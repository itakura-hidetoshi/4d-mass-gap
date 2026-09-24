import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Probability mean bounded by the L2 energy

On a probability space, the absolute mean of a real L2 function is bounded by
the square root of its second moment:

  | integral f dμ | <= sqrt (integral f^2 dμ).

This is the coefficient-one Cauchy--Schwarz estimate used for the direct term
in physical source-update decompositions.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Probability-space Cauchy--Schwarz with the constant function one. -/
theorem integral_abs_le_sqrt_integral_sq_of_memLp_two_probability
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    [IsProbabilityMeasure μ]
    (f : α → ℝ)
    (hf : MemLp f 2 μ) :
    |∫ x, f x ∂μ| ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  have hfOfReal : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hf
  have hOne : MemLp (fun _ : α => (1 : ℝ)) 2 μ :=
    memLp_const 1
  have hOneOfReal :
      MemLp (fun _ : α => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hOne
  have hHolderRaw :=
    integral_mul_norm_le_Lp_mul_Lq
      Real.HolderConjugate.two_two hfOfReal hOneOfReal
  have hFSq :
      (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) =
        ∫ x, f x ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    calc
      ‖f x‖ ^ (2 : ℝ) = ‖f x‖ ^ (2 : ℕ) :=
        Real.rpow_two _
      _ = f x ^ 2 := by
        simp only [Real.norm_eq_abs, sq_abs]
  have hOneSq :
      (∫ x : α, ‖(1 : ℝ)‖ ^ (2 : ℝ) ∂μ) = 1 := by
    simp
  rw [hFSq, hOneSq] at hHolderRaw
  have hHolder :
      (∫ x, |f x| ∂μ) ≤
        Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
    simpa [Real.norm_eq_abs, Real.sqrt_eq_rpow] using hHolderRaw
  exact
    (abs_integral_le_integral_abs).trans hHolder

end

end MGAP4D.MathlibAnalytic
