import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureProduct
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

/-- The iterated weighted Gram integral of any real Hilbert-kernel feature is
the squared norm of its Bochner moment.

This is the generic analytic strictness identity needed after a nonzero Fock
component has been produced.  It depends only on the Hilbert feature
realization and Bochner integration, not on any Wilson or lattice structure. -/
theorem RealHilbertKernelFeature.weighted_inner_doubleIntegral_eq_norm_integral_sq
    {X : Type} [MeasurableSpace X]
    {kernel : X → X → ℝ}
    (C : RealHilbertKernelFeature X kernel)
    (μ : Measure X)
    (a : X → ℝ)
    (hIntegrable : Integrable (fun x => a x • C.feature x) μ) :
    (∫ x, ∫ y,
      inner ℝ (a x • C.feature x) (a y • C.feature y) ∂μ ∂μ) =
      ‖∫ x, a x • C.feature x ∂μ‖ ^ 2 := by
  let M : C.FeatureHilbert := ∫ x, a x • C.feature x ∂μ
  calc
    (∫ x, ∫ y,
      inner ℝ (a x • C.feature x) (a y • C.feature y) ∂μ ∂μ) =
        ∫ x, inner ℝ (a x • C.feature x) M ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact integral_inner hIntegrable (a x • C.feature x)
    _ = ∫ x, inner ℝ M (a x • C.feature x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (real_inner_comm (a x • C.feature x) M).symm
    _ = inner ℝ M M := integral_inner hIntegrable M
    _ = ‖M‖ ^ 2 := inner_self_eq_norm_sq_to_K M
    _ = ‖∫ x, a x • C.feature x ∂μ‖ ^ 2 := rfl

/-- A nonzero weighted Hilbert-feature moment makes its iterated Gram integral
strictly positive.  Thus once a Taylor/Fock component is known not to vanish,
no scalar cancellation argument is needed to obtain strictness of the
corresponding positive-semidefinite quadratic form. -/
theorem RealHilbertKernelFeature.weighted_inner_doubleIntegral_pos_of_integral_ne_zero
    {X : Type} [MeasurableSpace X]
    {kernel : X → X → ℝ}
    (C : RealHilbertKernelFeature X kernel)
    (μ : Measure X)
    (a : X → ℝ)
    (hIntegrable : Integrable (fun x => a x • C.feature x) μ)
    (hMoment : (∫ x, a x • C.feature x ∂μ) ≠ 0) :
    0 < ∫ x, ∫ y,
      inner ℝ (a x • C.feature x) (a y • C.feature y) ∂μ ∂μ := by
  rw [C.weighted_inner_doubleIntegral_eq_norm_integral_sq μ a hIntegrable]
  exact pow_pos (norm_pos_iff.mpr hMoment) 2

end

end MathlibAnalytic
end MGAP4D