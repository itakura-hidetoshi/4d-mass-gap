import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureAddMomentStrictness
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The weighted Bochner moment of a nonnegatively scaled Hilbert feature is
the square-root scalar multiple of the original weighted moment. -/
theorem RealHilbertKernelFeature.nonnegSMul_weighted_integral_eq_sqrt_smul
    {X : Type} [MeasurableSpace X]
    {kernel : X → X → ℝ}
    (C : RealHilbertKernelFeature X kernel)
    (μ : Measure X)
    (a : X → ℝ)
    (c : ℝ) (hc : 0 ≤ c) :
    (∫ x,
      a x • (RealHilbertKernelFeature.nonnegSMul c hc C).feature x ∂μ) =
      Real.sqrt c • (∫ x, a x • C.feature x ∂μ) := by
  calc
    (∫ x,
      a x • (RealHilbertKernelFeature.nonnegSMul c hc C).feature x ∂μ) =
        ∫ x, Real.sqrt c • (a x • C.feature x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simpa [RealHilbertKernelFeature.nonnegSMul, smul_smul]
    _ = Real.sqrt c • (∫ x, a x • C.feature x ∂μ) := by
      exact integral_smul (Real.sqrt c) (fun x => a x • C.feature x)

/-- A nonzero square-root-scaled right moment remains nonzero after adjoining
an arbitrary left feature.  This packages the two cancellation-free operations
used by one successor step of the finite exponential/Fock construction. -/
theorem RealHilbertKernelFeature.add_nonnegSMul_weighted_integral_ne_zero_of_right
    {X : Type} [MeasurableSpace X]
    {kernel₁ kernel₂ : X → X → ℝ}
    (C₁ : RealHilbertKernelFeature X kernel₁)
    (C₂ : RealHilbertKernelFeature X kernel₂)
    (μ : Measure X)
    (a : X → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hIntegrable :
      Integrable
        (fun x => a x •
          (RealHilbertKernelFeature.add C₁
            (RealHilbertKernelFeature.nonnegSMul c hc C₂)).feature x) μ)
    (hRight :
      Real.sqrt c • (∫ x, a x • C₂.feature x ∂μ) ≠ 0) :
    (∫ x,
      a x •
        (RealHilbertKernelFeature.add C₁
          (RealHilbertKernelFeature.nonnegSMul c hc C₂)).feature x ∂μ) ≠ 0 := by
  apply RealHilbertKernelFeature.add_weighted_integral_ne_zero_of_right
    C₁ (RealHilbertKernelFeature.nonnegSMul c hc C₂) μ a hIntegrable
  rw [RealHilbertKernelFeature.nonnegSMul_weighted_integral_eq_sqrt_smul]
  exact hRight

end

end MathlibAnalytic
end MGAP4D