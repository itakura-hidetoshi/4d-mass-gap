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
  have hR :=
    realIntegralWeightedProbabilityMeasure_integral
      μ (fun x => w x * r x) f hwrInt hwrNonneg hwrMassPos
  have hS :=
    realIntegralWeightedProbabilityMeasure_integral
      μ (fun x => w x * s x) f hwsInt hwsNonneg hwsMassPos
  have hRJoint :
      (∫ x, (w x * r x) * f x ∂μ) =
        ∫ x, w x * (f x * r x) ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hSJoint :
      (∫ x, (w x * s x) * f x ∂μ) =
        ∫ x, w x * (f x * s x) ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hR, hS, hRJoint, hSJoint]
  field_simp [ne_of_gt hwrMassPos, ne_of_gt hwsMassPos]
  <;> ring

end

end MathlibAnalytic
end MGAP4D
