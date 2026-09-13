import MGAP4D.MathlibAnalytic.RealIntegralCrossRatioTransport
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The unnormalized covariance numerator of two observables under a real
weight `w`.  No probability normalization is built into this definition. -/
def realIntegralWeightedCovarianceNumerator
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w f g : α → ℝ) : ℝ :=
  (∫ x, w x ∂μ) * (∫ x, w x * (f x * g x) ∂μ) -
    (∫ x, w x * f x ∂μ) * (∫ x, w x * g x ∂μ)

/-- Multiplying the right observable by a scalar multiplies the unnormalized
weighted covariance numerator by the same scalar.  No normalization or
integrability hypotheses are needed. -/
theorem realIntegralWeightedCovarianceNumerator_const_mul_right
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w f g : α → ℝ)
    (c : ℝ) :
    realIntegralWeightedCovarianceNumerator μ w f (fun x => c * g x) =
      c * realIntegralWeightedCovarianceNumerator μ w f g := by
  rfl

/-- A four-integral cross-ratio defect with common left weight `a` is exactly
the unnormalized covariance numerator of the target ratio `p/q` and source
ratio `r/s` under the reference weight `a*q*s`.

The only hypotheses are the pointwise nonvanishing conditions needed to form
and cancel the two ratios.  No probability normalization, independence, or
positivity assumption is used. -/
theorem real_integral_crossRatio_defect_eq_weightedCovarianceNumerator
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (a p q r s : α → ℝ)
    (hq : ∀ x, q x ≠ 0)
    (hs : ∀ x, s x ≠ 0) :
    (∫ x, a x * p x * r x ∂μ) * (∫ x, a x * q x * s x ∂μ) -
        (∫ x, a x * p x * s x ∂μ) * (∫ x, a x * q x * r x ∂μ) =
      realIntegralWeightedCovarianceNumerator μ
        (fun x => a x * q x * s x)
        (fun x => p x / q x)
        (fun x => r x / s x) := by
  unfold realIntegralWeightedCovarianceNumerator
  have hJoint :
      (∫ x, (a x * q x * s x) * ((p x / q x) * (r x / s x)) ∂μ) =
        ∫ x, a x * p x * r x ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    field_simp [hq x, hs x]
    <;> ring
  have hTarget :
      (∫ x, (a x * q x * s x) * (p x / q x) ∂μ) =
        ∫ x, a x * p x * s x ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    field_simp [hq x]
    <;> ring
  have hSource :
      (∫ x, (a x * q x * s x) * (r x / s x) ∂μ) =
        ∫ x, a x * q x * r x ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    field_simp [hs x]
    <;> ring
  rw [hJoint, hTarget, hSource]
  ring

end

end MathlibAnalytic
end MGAP4D
