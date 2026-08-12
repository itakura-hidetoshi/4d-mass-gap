import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureExponentialPartialMomentStrictness
import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureKernelMomentNonzero

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A nonzero positive-degree scalar kernel moment produces a nonzero Bochner
moment in the corresponding successor finite exponential/Fock feature whenever
the coupling is strictly positive.

The proof is cancellation-free: the scalar moment first gives a nonzero
square-root-scaled degree-`m+1` Hilbert moment, and the direct-sum projection in
`exponentialPartial_succ_weighted_integral_ne_zero_of_top` prevents all lower
Taylor degrees from cancelling that top component. -/
theorem
    RealHilbertKernelFeature.exponentialPartial_succ_weighted_integral_ne_zero_of_kernel_pow_moment_ne_zero
    {X : Type} [MeasurableSpace X]
    {kernel : X → X → ℝ}
    (C : RealHilbertKernelFeature X kernel)
    (μ : Measure X)
    (a : X → ℝ)
    (c : ℝ) (hc : 0 < c)
    (m : ℕ)
    (hPow :
      Integrable (fun x => a x • (C.pow (m + 1)).feature x) μ)
    (hPartial :
      Integrable
        (fun x => a x • (C.exponentialPartial c hc.le (m + 1)).feature x)
        μ)
    (x₀ : X)
    (hmoment :
      (∫ x, a x * kernel x₀ x ^ (m + 1) ∂μ) ≠ 0) :
    (∫ x, a x • (C.exponentialPartial c hc.le (m + 1)).feature x ∂μ) ≠ 0 := by
  have hCoefficient :
      0 < c ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) := by
    exact div_pos (pow_pos hc _) (by positivity)
  have hTop :
      Real.sqrt (c ^ (m + 1) / (Nat.factorial (m + 1) : ℝ)) •
        (∫ x, a x • (C.pow (m + 1)).feature x ∂μ) ≠ 0 :=
    RealHilbertKernelFeature.pow_scaled_integral_ne_zero
      C μ a (m + 1)
      (c ^ (m + 1) / (Nat.factorial (m + 1) : ℝ))
      hCoefficient hPow x₀ hmoment
  exact
    RealHilbertKernelFeature.exponentialPartial_succ_weighted_integral_ne_zero_of_top
      C μ a c hc.le m hPartial hTop

end

end MathlibAnalytic
end MGAP4D