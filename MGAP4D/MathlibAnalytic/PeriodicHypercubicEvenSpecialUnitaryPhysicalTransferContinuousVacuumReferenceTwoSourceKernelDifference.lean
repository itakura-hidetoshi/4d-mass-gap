import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTwoSourceChangeCrossRatio
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Pure algebraic linearization of the four-integral two-tilt defect.

This form introduces no quotient and no new measure-theoretic hypothesis.  It
separates the change of the weighted observable numerator from the change of
the normalizing mass, which is the exact interface needed before exposing a
source-kernel difference. -/
theorem realIntegral_twoTilt_crossRatio_defect_eq_integralDifference_defect
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w r s f : α → ℝ) :
    (∫ x, w x * f x * r x ∂μ) * (∫ x, w x * s x ∂μ) -
        (∫ x, w x * f x * s x ∂μ) * (∫ x, w x * r x ∂μ) =
      (∫ x, w x * s x ∂μ) *
          ((∫ x, w x * f x * r x ∂μ) -
            ∫ x, w x * f x * s x ∂μ) -
        (∫ x, w x * f x * s x ∂μ) *
          ((∫ x, w x * r x ∂μ) -
            ∫ x, w x * s x ∂μ) := by
  ring

/-- Under exactly the integrability needed for integral subtraction, the
quotient-free two-tilt defect is linear in the pointwise source-tilt difference
`r - s`.

No likelihood ratio `r / s` is formed.  This theorem therefore preserves a
future distance-sensitive estimate on the source change itself. -/
theorem realIntegral_twoTilt_crossRatio_defect_eq_sourceDifference_defect
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w r s f : α → ℝ)
    (hwrInt : Integrable (fun x => w x * r x) μ)
    (hwsInt : Integrable (fun x => w x * s x) μ)
    (hwfrInt : Integrable (fun x => w x * f x * r x) μ)
    (hwfsInt : Integrable (fun x => w x * f x * s x) μ) :
    (∫ x, w x * f x * r x ∂μ) * (∫ x, w x * s x ∂μ) -
        (∫ x, w x * f x * s x ∂μ) * (∫ x, w x * r x ∂μ) =
      (∫ x, w x * s x ∂μ) *
          (∫ x, w x * f x * (r x - s x) ∂μ) -
        (∫ x, w x * f x * s x ∂μ) *
          (∫ x, w x * (r x - s x) ∂μ) := by
  have hObsSub :
      (∫ x, w x * f x * (r x - s x) ∂μ) =
        (∫ x, w x * f x * r x ∂μ) -
          ∫ x, w x * f x * s x ∂μ := by
    rw [← integral_sub hwfrInt hwfsInt]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hMassSub :
      (∫ x, w x * (r x - s x) ∂μ) =
        (∫ x, w x * r x ∂μ) -
          ∫ x, w x * s x ∂μ := by
    rw [← integral_sub hwrInt hwsInt]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hObsSub, hMassSub]
  exact realIntegral_twoTilt_crossRatio_defect_eq_integralDifference_defect μ w r s f

/-- The normalized two-tilt expectation change is therefore expressed by a
literal source-tilt difference once the two weighted observable numerators are
integrable.  Both exact normalizing masses remain visible. -/
theorem realIntegralWeightedProbabilityMeasure_twoTilt_cross_mul_eq_sourceDifference_defect
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w r s f : α → ℝ)
    (hwrInt : Integrable (fun x => w x * r x) μ)
    (hwrNonneg : ∀ᵐ x ∂μ, 0 ≤ w x * r x)
    (hRMassPos : 0 < ∫ x, w x * r x ∂μ)
    (hwsInt : Integrable (fun x => w x * s x) μ)
    (hwsNonneg : ∀ᵐ x ∂μ, 0 ≤ w x * s x)
    (hSMassPos : 0 < ∫ x, w x * s x ∂μ)
    (hwfrInt : Integrable (fun x => w x * f x * r x) μ)
    (hwfsInt : Integrable (fun x => w x * f x * s x) μ) :
    (∫ x, w x * r x ∂μ) * (∫ x, w x * s x ∂μ) *
        ((∫ x, f x ∂realIntegralWeightedProbabilityMeasure μ (fun x => w x * r x)) -
          ∫ x, f x ∂realIntegralWeightedProbabilityMeasure μ (fun x => w x * s x)) =
      (∫ x, w x * s x ∂μ) *
          (∫ x, w x * f x * (r x - s x) ∂μ) -
        (∫ x, w x * f x * s x ∂μ) *
          (∫ x, w x * (r x - s x) ∂μ) := by
  rw [realIntegralWeightedProbabilityMeasure_twoTilt_cross_mul_eq_crossRatio_defect
    μ w r s f hwrInt hwrNonneg hRMassPos hwsInt hwsNonneg hSMassPos]
  exact realIntegral_twoTilt_crossRatio_defect_eq_sourceDifference_defect
    μ w r s f hwrInt hwsInt hwfrInt hwfsInt

end

end MathlibAnalytic
end MGAP4D
