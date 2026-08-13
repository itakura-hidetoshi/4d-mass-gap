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

/-- A nonzero Bochner moment of a Hilbert kernel feature has a nonzero kernel
evaluation against at least one genuine point of the original carrier.

No density-of-feature-span hypothesis is needed.  If every kernel evaluation
vanished, the moment would be orthogonal to every point feature.  Integrating
that orthogonality once more against the very same weighted feature would give
`⟪M,M⟫ = 0`, contradicting the assumed nonzero moment.  This is the exact
cancellation-free bridge from an abstract RKHS/Fock moment to a concrete kernel
transform value. -/
theorem RealHilbertKernelFeature.exists_weighted_kernel_integral_ne_zero_of_integral_ne_zero
    {X : Type} [MeasurableSpace X]
    {kernel : X → X → ℝ}
    (C : RealHilbertKernelFeature X kernel)
    (μ : Measure X)
    (a : X → ℝ)
    (hIntegrable : Integrable (fun x => a x • C.feature x) μ)
    (hMoment : (∫ x, a x • C.feature x ∂μ) ≠ 0) :
    ∃ y : X, (∫ x, a x * kernel x y ∂μ) ≠ 0 := by
  let g : X → C.FeatureHilbert := fun x => a x • C.feature x
  let M : C.FeatureHilbert := ∫ x, g x ∂μ
  have hM : M ≠ 0 := by
    simpa [M, g] using hMoment
  by_contra hNo
  have hAll : ∀ y : X, (∫ x, a x * kernel x y ∂μ) = 0 := by
    intro y
    by_contra hy
    exact hNo ⟨y, hy⟩
  have hOrth : ∀ y : X, inner ℝ M (C.feature y) = 0 := by
    intro y
    calc
      inner ℝ M (C.feature y) =
          ∫ x, inner ℝ (g x) (C.feature y) ∂μ := by
        symm
        exact integral_inner hIntegrable (C.feature y)
      _ = ∫ x, a x * kernel x y ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp [g]
        rw [real_inner_smul_left]
        rw [← C.kernel_eq_inner]
      _ = 0 := hAll y
  have hSelf : inner ℝ M M = 0 := by
    calc
      inner ℝ M M = ∫ x, inner ℝ M (g x) ∂μ := by
        symm
        exact integral_inner hIntegrable M
      _ = ∫ _x : X, (0 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp [g]
        rw [real_inner_smul_right, hOrth x, mul_zero]
      _ = 0 := by simp
  exact hM (inner_self_eq_zero.mp hSelf)

end

end MathlibAnalytic
end MGAP4D
