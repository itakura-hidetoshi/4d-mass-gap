import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

universe u v

variable {α : Type u} {H : Type v}
  [MeasurableSpace α]
  [NormedAddCommGroup H]
  [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- The real-Hilbert rank-one operator as an ordinary continuous bilinear map.

Mathlib's general `InnerProductSpace.rankOne` is sesquilinear in its second
vector over an arbitrary `RCLike` scalar field.  Over `ℝ` the inner product is
bilinear, so this ordinary bilinear packaging is the convenient form for
continuity and Bochner measurability arguments. -/
noncomputable def realHilbertRankOneBilinear :
    H →L[ℝ] H →L[ℝ] (H →L[ℝ] H) :=
  ((ContinuousLinearMap.smulRightL ℝ H H).comp
      (isBoundedBilinearMap_inner (𝕜 := ℝ) (E := H)).toContinuousLinearMap).flip

@[simp]
theorem realHilbertRankOneBilinear_apply (v w : H) :
    (realHilbertRankOneBilinear v) w =
      ((InnerProductSpace.rankOne ℝ) v) w := by
  ext x
  simp [realHilbertRankOneBilinear, InnerProductSpace.rankOne_apply]

/-- The self rank-one operator attached to a vector in a real Hilbert space:
`x ↦ ⟪v,x⟫ v`.

Keeping this bundled as a continuous linear map lets the geometric transfer
construction use Bochner integration directly, without choosing any basis. -/
noncomputable def realHilbertSelfRankOne (v : H) : H →L[ℝ] H :=
  (realHilbertRankOneBilinear v) v

@[simp]
theorem realHilbertSelfRankOne_eq_rankOne (v : H) :
    realHilbertSelfRankOne v = ((InnerProductSpace.rankOne ℝ) v) v := by
  simp [realHilbertSelfRankOne]

@[simp]
theorem realHilbertSelfRankOne_apply (v x : H) :
    realHilbertSelfRankOne v x = inner ℝ v x • v := by
  simp [realHilbertSelfRankOne, InnerProductSpace.rankOne_apply]

@[simp]
theorem realHilbertSelfRankOne_norm (v : H) :
    ‖realHilbertSelfRankOne v‖ = ‖v‖ ^ 2 := by
  rw [realHilbertSelfRankOne_eq_rankOne, InnerProductSpace.norm_rankOne]
  simp [pow_two]

/-- A strongly measurable Hilbert-valued feature gives a strongly measurable
field of self rank-one continuous operators. -/
theorem realHilbertSelfRankOne_aestronglyMeasurable
    {μ : Measure α} {v : α → H}
    (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun a => realHilbertSelfRankOne (v a)) μ := by
  have hdiag : Continuous (fun x : H => (x, x)) :=
    continuous_id.prodMk continuous_id
  have hbilin : Continuous
      (Function.uncurry
        (fun x y : H => (realHilbertRankOneBilinear x) y)) :=
    (realHilbertRankOneBilinear (H := H)).continuous₂
  have hcont : Continuous
      (fun x : H => (realHilbertRankOneBilinear x) x) := by
    simpa [Function.comp_def] using hbilin.comp hdiag
  simpa [realHilbertSelfRankOne] using
    hcont.comp_aestronglyMeasurable hv

/-- Square-integrability of a Hilbert feature is exactly the Bochner
integrability condition for its self rank-one operator field, because Mathlib's
rank-one norm is the product of the two vector norms. -/
theorem realHilbertSelfRankOne_integrable
    {μ : Measure α} {v : α → H}
    (hv : AEStronglyMeasurable v μ)
    (hv2 : Integrable (fun a => ‖v a‖ ^ 2) μ) :
    Integrable (fun a => realHilbertSelfRankOne (v a)) μ := by
  refine ⟨realHilbertSelfRankOne_aestronglyMeasurable hv, ?_⟩
  rw [← MeasureTheory.hasFiniteIntegral_norm_iff]
  simpa only [realHilbertSelfRankOne_norm] using hv2.hasFiniteIntegral

/-- Basis-free frame operator obtained by Bochner integrating the self rank-one
field of a square-integrable Hilbert feature.

The definition is total, as Mathlib's Bochner integral is total; the useful
application and norm theorems below are stated under the natural integrability
hypotheses. -/
noncomputable def realHilbertIntegratedSelfRankOne
    (μ : Measure α) (v : α → H) : H →L[ℝ] H :=
  ∫ a, realHilbertSelfRankOne (v a) ∂μ

/-- Evaluation of the integrated self-rank-one operator commutes with the
Bochner integral. -/
theorem realHilbertIntegratedSelfRankOne_apply
    {μ : Measure α} {v : α → H}
    (hv : AEStronglyMeasurable v μ)
    (hv2 : Integrable (fun a => ‖v a‖ ^ 2) μ)
    (x : H) :
    realHilbertIntegratedSelfRankOne μ v x =
      ∫ a, inner ℝ (v a) x • v a ∂μ := by
  rw [realHilbertIntegratedSelfRankOne,
    ContinuousLinearMap.integral_apply
      (realHilbertSelfRankOne_integrable hv hv2) x]
  apply integral_congr_ae
  filter_upwards with a
  exact realHilbertSelfRankOne_apply (v a) x

/-- The integrated self-rank-one operator has the sharp basis-free trace-style
norm bound `‖A_v‖ ≤ ∫ ‖v‖²`. -/
theorem realHilbertIntegratedSelfRankOne_norm_le_integral_sq_norm
    (μ : Measure α) (v : α → H) :
    ‖realHilbertIntegratedSelfRankOne μ v‖ ≤
      ∫ a, ‖v a‖ ^ 2 ∂μ := by
  calc
    ‖realHilbertIntegratedSelfRankOne μ v‖
        ≤ ∫ a, ‖realHilbertSelfRankOne (v a)‖ ∂μ := by
          exact MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ a, ‖v a‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with a
      exact realHilbertSelfRankOne_norm (v a)

/-- A uniform square-integral cap immediately becomes an operator-norm cap for
the integrated self-rank-one operator. -/
theorem realHilbertIntegratedSelfRankOne_norm_le
    {μ : Measure α} {v : α → H} {C : ℝ}
    (hC : ∫ a, ‖v a‖ ^ 2 ∂μ ≤ C) :
    ‖realHilbertIntegratedSelfRankOne μ v‖ ≤ C :=
  (realHilbertIntegratedSelfRankOne_norm_le_integral_sq_norm μ v).trans hC

end

end MathlibAnalytic
end MGAP4D
