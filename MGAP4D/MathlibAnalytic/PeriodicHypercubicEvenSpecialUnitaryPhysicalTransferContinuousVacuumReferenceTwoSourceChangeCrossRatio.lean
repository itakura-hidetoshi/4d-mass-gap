import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceSourceChangeCovariance
import MGAP4D.MathlibAnalytic.RealIntegralCrossRatioCovarianceLocalization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Cross-multiplying expectations under two independently tilted positive
weights removes both normalization denominators and leaves the literal
four-integral cross-ratio defect.

This quotient-free identity keeps both source tilts visible.  In particular,
it does not identify either normalized law with a conditional distribution and
does not divide one source tilt by the other. -/
theorem realIntegralWeightedProbabilityMeasure_twoTilt_cross_mul_eq_crossRatio_defect
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w r s f : α → ℝ)
    (hwrInt : Integrable (fun x => w x * r x) μ)
    (hwrNonneg : ∀ᵐ x ∂μ, 0 ≤ w x * r x)
    (hRMassPos : 0 < ∫ x, w x * r x ∂μ)
    (hwsInt : Integrable (fun x => w x * s x) μ)
    (hwsNonneg : ∀ᵐ x ∂μ, 0 ≤ w x * s x)
    (hSMassPos : 0 < ∫ x, w x * s x ∂μ) :
    (∫ x, w x * r x ∂μ) * (∫ x, w x * s x ∂μ) *
        ((∫ x, f x ∂realIntegralWeightedProbabilityMeasure μ (fun x => w x * r x)) -
          ∫ x, f x ∂realIntegralWeightedProbabilityMeasure μ (fun x => w x * s x)) =
      (∫ x, w x * f x * r x ∂μ) * (∫ x, w x * s x ∂μ) -
        (∫ x, w x * f x * s x ∂μ) * (∫ x, w x * r x ∂μ) := by
  have hR :=
    realIntegralWeightedProbabilityMeasure_integral
      μ (fun x => w x * r x) f hwrInt hwrNonneg hRMassPos
  have hS :=
    realIntegralWeightedProbabilityMeasure_integral
      μ (fun x => w x * s x) f hwsInt hwsNonneg hSMassPos
  have hRJoint :
      (∫ x, (w x * r x) * f x ∂μ) =
        ∫ x, w x * f x * r x ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hSJoint :
      (∫ x, (w x * s x) * f x ∂μ) =
        ∫ x, w x * f x * s x ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hR, hS, hRJoint, hSJoint]
  field_simp [ne_of_gt hRMassPos, ne_of_gt hSMassPos]
  <;> ring

/-- If the second tilt is pointwise nonzero, the quotient-free two-tilt defect
can additionally be localized by the existing four-integral cross-ratio API as
an unnormalized covariance numerator under the second tilted weight.

The nonvanishing hypothesis is intentionally explicit: the preceding theorem
is the preferred interface when source-distance information must be retained
without introducing a likelihood-ratio quotient. -/
theorem realIntegralWeightedProbabilityMeasure_twoTilt_cross_mul_eq_weightedCovarianceNumerator
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w r s f : α → ℝ)
    (hwrInt : Integrable (fun x => w x * r x) μ)
    (hwrNonneg : ∀ᵐ x ∂μ, 0 ≤ w x * r x)
    (hRMassPos : 0 < ∫ x, w x * r x ∂μ)
    (hwsInt : Integrable (fun x => w x * s x) μ)
    (hwsNonneg : ∀ᵐ x ∂μ, 0 ≤ w x * s x)
    (hSMassPos : 0 < ∫ x, w x * s x ∂μ)
    (hsNe : ∀ x, s x ≠ 0) :
    (∫ x, w x * r x ∂μ) * (∫ x, w x * s x ∂μ) *
        ((∫ x, f x ∂realIntegralWeightedProbabilityMeasure μ (fun x => w x * r x)) -
          ∫ x, f x ∂realIntegralWeightedProbabilityMeasure μ (fun x => w x * s x)) =
      realIntegralWeightedCovarianceNumerator μ
        (fun x => w x * s x) f (fun x => r x / s x) := by
  calc
    (∫ x, w x * r x ∂μ) * (∫ x, w x * s x ∂μ) *
          ((∫ x, f x ∂realIntegralWeightedProbabilityMeasure μ (fun x => w x * r x)) -
            ∫ x, f x ∂realIntegralWeightedProbabilityMeasure μ (fun x => w x * s x)) =
        (∫ x, w x * f x * r x ∂μ) * (∫ x, w x * s x ∂μ) -
          (∫ x, w x * f x * s x ∂μ) * (∫ x, w x * r x ∂μ) :=
      realIntegralWeightedProbabilityMeasure_twoTilt_cross_mul_eq_crossRatio_defect
        μ w r s f hwrInt hwrNonneg hRMassPos hwsInt hwsNonneg hSMassPos
    _ = realIntegralWeightedCovarianceNumerator μ
          (fun x => w x * s x) f (fun x => r x / s x) := by
      simpa using
        (real_integral_crossRatio_defect_eq_weightedCovarianceNumerator
          μ w f (fun _ => (1 : ℝ)) r s (by intro x; simp) hsNe)

end

end MathlibAnalytic
end MGAP4D
