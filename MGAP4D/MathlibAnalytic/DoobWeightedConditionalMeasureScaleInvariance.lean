import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureComparison
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Multiplying a nonnegative Doob weight by a positive finite constant does
not change its normalized weighted measure.  Finiteness of the constant is
enough for the `lintegral` scaling identity, so no measurability hypothesis on
the weight is needed. -/
theorem doobWeightedMeasure_mul_const_eq
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    (w : α → ℝ≥0∞)
    (c : ℝ≥0∞)
    (hcZero : c ≠ 0)
    (hcTop : c ≠ ∞) :
    doobWeightedMeasure μ (fun x => w x * c) =
      doobWeightedMeasure μ w := by
  have hMass :
      doobWeightMass μ (fun x => w x * c) =
        doobWeightMass μ w * c := by
    unfold doobWeightMass
    exact lintegral_mul_const' c w hcTop
  unfold doobWeightedMeasure
  apply withDensity_congr_ae
  filter_upwards with x
  simp only [doobWeightedDensity]
  rw [hMass]
  exact ENNReal.mul_div_mul_right _ _ hcZero hcTop

end

end MathlibAnalytic
end MGAP4D
