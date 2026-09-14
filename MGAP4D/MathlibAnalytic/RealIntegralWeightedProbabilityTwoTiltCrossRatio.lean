import MGAP4D.MathlibAnalytic.RealIntegralWeightedProbabilityNormalization
import MGAP4D.MathlibAnalytic.RealIntegralCrossRatioCovarianceLocalization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Cross-multiplying normalized expectations under two multiplicative tilts
of the same base weight removes both normalization denominators and exposes the
exact four-integral source-change defect.  No quotient between the two tilts is
introduced. -/
theorem realIntegralWeightedProbabilityMeasure_twoTilt_cross_mul_eq_crossRatioDefect
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w r s f : α → ℝ)
    (hwrInt : Integrable (fun x => w x * r x) μ)
    (hwrNonneg : ∀ᵐ x ∂μ, 0 ≤ w x * r x)
    (hwrMassPos : 0 < ∫ x, w x * r x ∂μ)
    (hwsInt : Integrable (fun x => w x * s x) μ)
    (hwsNonneg : ∀ᵐ x ∂μ, 0 ≤ w x * s x)
    (hwsMassPos : 0 < ∫ x, w x * s x ∂μ) :
    (∫ x, w x * r x ∂μ) * (∫ x, w x * s x ∂μ) *
        ((∫ x, f x ∂realIntegralWeightedProbabilityMeasure μ (fun x => w x * r x)) -
          ∫ x, f x ∂realIntegralWeightedProbabilityMeasure μ (fun x => w x * s x)) =
      (∫ x, w x * (f x * r x) ∂μ) * (∫ x, w x * s x ∂μ) -
        (∫ x, w x * (f x * s x) ∂μ) * (∫ x, w x * r x ∂μ) := by
  aesop

end

end MathlibAnalytic
end MGAP4D
