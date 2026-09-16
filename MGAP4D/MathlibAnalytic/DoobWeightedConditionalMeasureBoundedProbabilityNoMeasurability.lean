import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureComparison
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- A normalized Doob weighted measure has total mass one whenever its
normalizing mass is nonzero and finite.  No measurability hypothesis on the
weight is needed: the finite constant multiplier is pulled through the
lintegral with `lintegral_mul_const'`. -/
theorem doobWeightedMeasure_measure_univ_without_measurability
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    (w : α → ℝ≥0∞)
    (hMassZero : doobWeightMass μ w ≠ 0)
    (hMassTop : doobWeightMass μ w ≠ ∞) :
    doobWeightedMeasure μ w Set.univ = 1 := by
  rw [doobWeightedMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  change ∫⁻ x, w x / doobWeightMass μ w ∂μ = 1
  simp only [div_eq_mul_inv]
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hMassZero)]
  change doobWeightMass μ w * (doobWeightMass μ w)⁻¹ = 1
  exact ENNReal.mul_inv_cancel hMassZero hMassTop

/-- On a probability reference measure, positive lower and finite upper
pointwise bounds make the normalized Doob weighted measure a probability
measure without any separate measurability hypothesis on the weight. -/
theorem doobWeightedMeasure_isProbabilityMeasure_of_bounds_without_measurability
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    [IsProbabilityMeasure μ]
    (w : α → ℝ≥0∞)
    (m M : ℝ≥0∞)
    (hm : 0 < m)
    (hM : M < ∞)
    (hLower : ∀ x, m ≤ w x)
    (hUpper : ∀ x, w x ≤ M) :
    IsProbabilityMeasure (doobWeightedMeasure μ w) := by
  have hMassLower : m ≤ doobWeightMass μ w :=
    doobWeightMass_lower_bound μ w m hLower
  have hMassUpper : doobWeightMass μ w ≤ M :=
    doobWeightMass_upper_bound μ w M hUpper
  refine ⟨doobWeightedMeasure_measure_univ_without_measurability μ w ?_ ?_⟩
  · exact ne_of_gt (lt_of_lt_of_le hm hMassLower)
  · exact ne_of_lt (lt_of_le_of_lt hMassUpper hM)

end

end MathlibAnalytic
end MGAP4D
