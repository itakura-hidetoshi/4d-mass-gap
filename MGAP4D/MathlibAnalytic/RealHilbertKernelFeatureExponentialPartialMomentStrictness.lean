import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureNonnegSMulMomentStrictness

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A nonzero top Taylor/Fock component cannot be cancelled by the lower
finite exponential degrees.

The successor finite exponential feature is a Hilbert `L²` direct sum of the
previous partial feature and the square-root-scaled degree-`m+1` tensor feature.
Consequently the right-coordinate Bochner moment detects the top component
without any orthogonality assumption between scalar Taylor terms and without
any Haar-sector vanishing statement. -/
theorem RealHilbertKernelFeature.exponentialPartial_succ_weighted_integral_ne_zero_of_top
    {X : Type} [MeasurableSpace X]
    {kernel : X → X → ℝ}
    (C : RealHilbertKernelFeature X kernel)
    (μ : Measure X)
    (a : X → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (m : ℕ)
    (hIntegrable :
      Integrable
        (fun x =>
          a x • (RealHilbertKernelFeature.exponentialPartial C c hc (m + 1)).feature x)
        μ)
    (hTop :
      Real.sqrt (c ^ (m + 1) / (Nat.factorial (m + 1) : ℝ)) •
        (∫ x, a x • (RealHilbertKernelFeature.pow C (m + 1)).feature x ∂μ) ≠ 0) :
    (∫ x,
      a x • (RealHilbertKernelFeature.exponentialPartial C c hc (m + 1)).feature x
      ∂μ) ≠ 0 := by
  have hCoefficient :
      0 ≤ c ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) := by
    exact div_nonneg (pow_nonneg hc _) (by positivity)
  have hIntegrable' :
      Integrable
        (fun x =>
          a x •
            (RealHilbertKernelFeature.add
              (RealHilbertKernelFeature.exponentialPartial C c hc m)
              (RealHilbertKernelFeature.nonnegSMul
                (c ^ (m + 1) / (Nat.factorial (m + 1) : ℝ))
                hCoefficient
                (RealHilbertKernelFeature.pow C (m + 1)))).feature x)
        μ := by
    simpa [RealHilbertKernelFeature.exponentialPartial,
      RealHilbertKernelFeature.exponentialPartialKernel] using hIntegrable
  have hNonzero :=
    RealHilbertKernelFeature.add_nonnegSMul_weighted_integral_ne_zero_of_right
      (RealHilbertKernelFeature.exponentialPartial C c hc m)
      (RealHilbertKernelFeature.pow C (m + 1))
      μ a
      (c ^ (m + 1) / (Nat.factorial (m + 1) : ℝ))
      hCoefficient hIntegrable' hTop
  simpa [RealHilbertKernelFeature.exponentialPartial,
    RealHilbertKernelFeature.exponentialPartialKernel] using hNonzero

end

end MathlibAnalytic
end MGAP4D