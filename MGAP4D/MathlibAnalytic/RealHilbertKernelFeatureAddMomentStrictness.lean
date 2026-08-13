import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureProduct
import Mathlib.MeasureTheory.Function.L2Space
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

/-- A protected nonzero right-component moment makes the complete direct-sum
Hilbert Gram quadratic form strictly positive.

This is the Bochner version of cancellation-free PSD protection.  No sign is
assigned to a scalar cross-degree coefficient: the protected component is
recovered by the continuous right projection, hence the full moment is
nonzero, and the complete Gram form is its squared norm. -/
theorem RealHilbertKernelFeature.add_weighted_iterated_inner_pos_of_right
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
    0 < ∫ x, ∫ y,
      inner ℝ
        (a x • (RealHilbertKernelFeature.add C₁ C₂).feature x)
        (a y • (RealHilbertKernelFeature.add C₁ C₂).feature y)
      ∂μ ∂μ := by
  let g := fun x => a x • (RealHilbertKernelFeature.add C₁ C₂).feature x
  let M := ∫ x, g x ∂μ
  have hMoment : M ≠ 0 := by
    dsimp [M, g]
    exact RealHilbertKernelFeature.add_weighted_integral_ne_zero_of_right
      C₁ C₂ μ a hIntegrable hRight
  have hGram :
      (∫ x, ∫ y, inner ℝ (g x) (g y) ∂μ ∂μ) = ‖M‖ ^ 2 := by
    calc
      (∫ x, ∫ y, inner ℝ (g x) (g y) ∂μ ∂μ) =
          ∫ x, inner ℝ (g x) M ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact integral_inner hIntegrable (g x)
      _ = ∫ x, inner ℝ M (g x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact (real_inner_comm (g x) M).symm
      _ = inner ℝ M M := integral_inner hIntegrable M
      _ = ‖M‖ ^ 2 := inner_self_eq_norm_sq_to_K M
  change 0 < ∫ x, ∫ y, inner ℝ (g x) (g y) ∂μ ∂μ
  rw [hGram]
  exact pow_pos (norm_pos_iff.mpr hMoment) 2

end

end MathlibAnalytic
end MGAP4D