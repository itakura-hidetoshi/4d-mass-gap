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
  rfl

end

end MathlibAnalytic
end MGAP4D
