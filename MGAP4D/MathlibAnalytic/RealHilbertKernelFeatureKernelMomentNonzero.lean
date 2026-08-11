import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureProduct
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

universe u v

/-- A nonzero scalar kernel moment detects a nonzero Bochner moment of any
real Hilbert feature realization.

For a weighted feature `x ↦ a x • feature x`, pairing its Bochner integral
against the fixed feature vector at `x₀` gives exactly
`∫ x, a x * kernel x₀ x`. Hence a nonzero scalar kernel moment forces the
Hilbert-valued moment itself to be nonzero. -/
theorem RealHilbertKernelFeature.integral_ne_zero_of_kernel_moment_ne_zero
    {X : Type u}
    {kernel : X → X → ℝ}
    [MeasurableSpace X]
    (C : RealHilbertKernelFeature X kernel)
    (mu : Measure X)
    (a : X → ℝ)
    (ha : Integrable (fun x => a x • C.feature x) mu)
    (x₀ : X)
    (hmoment : (∫ x, a x * kernel x₀ x ∂mu) ≠ 0) :
    (∫ x, a x • C.feature x ∂mu) ≠ 0 := by
  intro hzero
  have hInner := integral_inner ha (C.feature x₀)
  have hScalar : (∫ x, a x * kernel x₀ x ∂mu) = 0 := by
    calc
      (∫ x, a x * kernel x₀ x ∂mu) =
          ∫ x, inner ℝ (C.feature x₀) (a x • C.feature x) ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [real_inner_smul_right, ← C.kernel_eq_inner]
      _ = inner ℝ (C.feature x₀) (∫ x, a x • C.feature x ∂mu) := hInner
      _ = 0 := by rw [hzero, inner_zero]
  exact hmoment hScalar

/-- Degree-`n` specialization for tensor-power features.  A nonzero scalar
moment against `kernel x₀ x ^ n` forces the corresponding degree-`n` Hilbert
tensor-feature Bochner moment to be nonzero. -/
theorem RealHilbertKernelFeature.pow_integral_ne_zero_of_kernel_pow_moment_ne_zero
    {X : Type u}
    {kernel : X → X → ℝ}
    [MeasurableSpace X]
    (C : RealHilbertKernelFeature X kernel)
    (mu : Measure X)
    (a : X → ℝ)
    (n : ℕ)
    (ha : Integrable (fun x => a x • (C.pow n).feature x) mu)
    (x₀ : X)
    (hmoment : (∫ x, a x * kernel x₀ x ^ n ∂mu) ≠ 0) :
    (∫ x, a x • (C.pow n).feature x ∂mu) ≠ 0 := by
  exact (C.pow n).integral_ne_zero_of_kernel_moment_ne_zero
    mu a ha x₀ hmoment

/-- A strictly positive Taylor/Fock coefficient cannot annihilate a nonzero
feature moment after the square-root scaling used by `nonnegSMul`. -/
theorem RealHilbertKernelFeature.sqrt_smul_ne_zero_of_pos
    {H : Type v}
    [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    (c : ℝ) (hc : 0 < c)
    (v : H) (hv : v ≠ 0) :
    Real.sqrt c • v ≠ 0 := by
  exact smul_ne_zero (ne_of_gt (Real.sqrt_pos.2 hc)) hv

/-- Consequently, once a degree-`n` tensor-feature moment is nonzero and the
Taylor coefficient is positive, the corresponding scaled Fock component is
nonzero. -/
theorem RealHilbertKernelFeature.pow_scaled_integral_ne_zero
    {X : Type u}
    {kernel : X → X → ℝ}
    [MeasurableSpace X]
    (C : RealHilbertKernelFeature X kernel)
    (mu : Measure X)
    (a : X → ℝ)
    (n : ℕ)
    (coefficient : ℝ) (hcoefficient : 0 < coefficient)
    (ha : Integrable (fun x => a x • (C.pow n).feature x) mu)
    (x₀ : X)
    (hmoment : (∫ x, a x * kernel x₀ x ^ n ∂mu) ≠ 0) :
    Real.sqrt coefficient •
        (∫ x, a x • (C.pow n).feature x ∂mu) ≠ 0 := by
  apply RealHilbertKernelFeature.sqrt_smul_ne_zero_of_pos
    coefficient hcoefficient
  exact C.pow_integral_ne_zero_of_kernel_pow_moment_ne_zero
    mu a n ha x₀ hmoment

end

end MathlibAnalytic
end MGAP4D