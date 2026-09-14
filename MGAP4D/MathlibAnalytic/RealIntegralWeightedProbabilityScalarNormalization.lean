import MGAP4D.MathlibAnalytic.RealIntegralWeightedProbabilityNormalization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Multiplying an ENNReal Doob weight by a nonzero finite scalar does not
change its normalized weighted measure.  The only analytic input is
almost-everywhere measurability of the original weight, needed to pull the
constant through the `lintegral`; cancellation itself is exact. -/
theorem doobWeightedMeasure_const_mul
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w : α → ENNReal)
    (c : ENNReal)
    (hw : AEMeasurable w μ)
    (hcZero : c ≠ 0)
    (hcTop : c ≠ ∞) :
    doobWeightedMeasure μ (fun x => c * w x) =
      doobWeightedMeasure μ w := by
  unfold doobWeightedMeasure doobWeightedDensity
  apply congrArg (fun ρ => μ.withDensity ρ)
  funext x
  unfold doobWeightMass
  rw [lintegral_const_mul'' c hw]
  exact ENNReal.mul_div_mul_left
    (w x) (∫⁻ y, w y ∂μ) hcZero hcTop

/-- Positive scalar rescaling of a real weight leaves the normalized real
weighted probability measure unchanged.  No positivity or finiteness
hypothesis on the total mass is needed here: those are needed only when one
wants a probability receipt for the totalized normalization construction. -/
theorem realIntegralWeightedProbabilityMeasure_const_mul
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w : α → ℝ)
    (c : ℝ)
    (hw : AEMeasurable w μ)
    (hc : 0 < c) :
    realIntegralWeightedProbabilityMeasure μ (fun x => c * w x) =
      realIntegralWeightedProbabilityMeasure μ w := by
  unfold realIntegralWeightedProbabilityMeasure
  have hwOfReal :
      AEMeasurable (fun x => ENNReal.ofReal (w x)) μ := by
    simpa [Function.comp_def] using
      ENNReal.measurable_ofReal.comp_aemeasurable hw
  have hcZero : ENNReal.ofReal c ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hc)
  have hcTop : ENNReal.ofReal c ≠ ∞ :=
    ne_of_lt ENNReal.ofReal_lt_top
  have hScaled :
      (fun x => ENNReal.ofReal (c * w x)) =
        (fun x => ENNReal.ofReal c * ENNReal.ofReal (w x)) := by
    funext x
    rw [ENNReal.ofReal_mul hc.le]
  rw [hScaled]
  exact doobWeightedMeasure_const_mul
    μ (fun x => ENNReal.ofReal (w x)) (ENNReal.ofReal c)
    hwOfReal hcZero hcTop

end

end MathlibAnalytic
end MGAP4D
