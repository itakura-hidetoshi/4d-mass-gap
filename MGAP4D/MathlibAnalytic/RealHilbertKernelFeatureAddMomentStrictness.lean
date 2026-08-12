import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureProduct
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- A nonzero right-component Bochner moment cannot disappear after adjoining
an arbitrary left Hilbert feature through the `L²` product constructor.

This is the cancellation-free separation step used by finite Fock sums: the
right coordinate is recovered by Mathlib's continuous projection `WithLp.sndL`,
which commutes with the Bochner integral. -/
theorem RealHilbertKernelFeature.add_weighted_integral_ne_zero_of_right
    {X : Type} [MeasurableSpace X]
    {kernel₁ kernel₂ : X → X → ℝ}
    (C₁ : RealHilbertKernelFeature X kernel₁)
    (C₂ : RealHilbertKernelFeature X kernel₂)
    (μ : Measure X)
    (a : X → ℝ)
    (hIntegrable :
      Integrable (fun x => a x • (RealHilbertKernelFeature.add C₁ C₂).feature x) μ)
    (hRight :
      (∫ x, a x • C₂.feature x ∂μ) ≠ 0) :
    (∫ x, a x • (RealHilbertKernelFeature.add C₁ C₂).feature x ∂μ) ≠ 0 := by
  intro hzero
  apply hRight
  have hproj :=
    (WithLp.sndL 2 ℝ C₁.FeatureHilbert C₂.FeatureHilbert).integral_comp_comm hIntegrable
  have hzeroProjected :
      (WithLp.sndL 2 ℝ C₁.FeatureHilbert C₂.FeatureHilbert)
        (∫ x, a x • (RealHilbertKernelFeature.add C₁ C₂).feature x ∂μ) = 0 := by
    have h := congrArg
      (WithLp.sndL 2 ℝ C₁.FeatureHilbert C₂.FeatureHilbert) hzero
    simpa using h
  have hproj0 :
      (∫ x,
        (WithLp.sndL 2 ℝ C₁.FeatureHilbert C₂.FeatureHilbert)
          (a x • (RealHilbertKernelFeature.add C₁ C₂).feature x) ∂μ) = 0 :=
    hproj.trans hzeroProjected
  simpa [RealHilbertKernelFeature.add] using hproj0

end

end MathlibAnalytic
end MGAP4D