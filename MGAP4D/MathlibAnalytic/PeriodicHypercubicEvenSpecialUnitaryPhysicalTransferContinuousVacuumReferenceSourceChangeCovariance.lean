import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceProbability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Cross-multiplying the expectations under a positive reference weight and
its multiplicative source tilt removes both normalizing denominators and leaves
exactly the unnormalized weighted covariance numerator.

This is a generic normalization identity.  It does not identify either
normalized law with a conditional distribution. -/
theorem realIntegralWeightedProbabilityMeasure_sourceChange_cross_mul_eq_weightedCovarianceNumerator
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w r f : α → ℝ)
    (hwInt : Integrable w μ)
    (hwNonneg : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hMassPos : 0 < ∫ x, w x ∂μ)
    (hwrInt : Integrable (fun x => w x * r x) μ)
    (hwrNonneg : ∀ᵐ x ∂μ, 0 ≤ w x * r x)
    (hTiltMassPos : 0 < ∫ x, w x * r x ∂μ) :
    (∫ x, w x ∂μ) * (∫ x, w x * r x ∂μ) *
        ((∫ x, f x ∂realIntegralWeightedProbabilityMeasure μ (fun x => w x * r x)) -
          ∫ x, f x ∂realIntegralWeightedProbabilityMeasure μ w) =
      realIntegralWeightedCovarianceNumerator μ w f r := by
  have hTilt :=
    realIntegralWeightedProbabilityMeasure_integral
      μ (fun x => w x * r x) f hwrInt hwrNonneg hTiltMassPos
  have hBase :=
    realIntegralWeightedProbabilityMeasure_integral
      μ w f hwInt hwNonneg hMassPos
  have hJoint :
      (∫ x, (w x * r x) * f x ∂μ) =
        ∫ x, w x * (f x * r x) ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hTilt, hBase, hJoint]
  unfold realIntegralWeightedCovarianceNumerator
  field_simp [ne_of_gt hMassPos, ne_of_gt hTiltMassPos]
  <;> ring

end

end MathlibAnalytic
end MGAP4D
