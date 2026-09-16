import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureScaleInvariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Two successive normalized Doob weightings compose to the normalized product
weight, provided the normalization mass of the first weight is nonzero and
finite.

The second normalization mass is computed exactly as
`Z(r * v) / Z(r)`.  No positivity or finiteness hypothesis on `Z(r * v)` is
needed for the measure identity itself. -/
theorem doobWeightedMeasure_compose
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    (r v : α → ℝ≥0∞)
    (hr : AEMeasurable r μ)
    (hv : AEMeasurable v μ)
    (hMassRZero : doobWeightMass μ r ≠ 0)
    (hMassRTop : doobWeightMass μ r ≠ ∞) :
    doobWeightedMeasure (doobWeightedMeasure μ r) v =
      doobWeightedMeasure μ (fun x => r x * v x) := by
  have hRawDensityMeas :
      AEMeasurable (doobWeightedDensity μ r) μ := by
    unfold doobWeightedDensity
    exact hr.div_const _
  have hOuterDensityMeas :
      AEMeasurable
        (doobWeightedDensity
          (μ.withDensity (doobWeightedDensity μ r)) v) μ := by
    unfold doobWeightedDensity
    exact hv.div_const _
  have hMass :
      doobWeightMass (doobWeightedMeasure μ r) v =
        doobWeightMass μ (fun x => r x * v x) / doobWeightMass μ r := by
    unfold doobWeightMass
    change
      (∫⁻ x, v x ∂μ.withDensity (doobWeightedDensity μ r)) =
        (∫⁻ x, r x * v x ∂μ) / (∫⁻ x, r x ∂μ)
    rw [lintegral_withDensity_eq_lintegral_mul₀ hRawDensityMeas hv]
    simp only [doobWeightedDensity, doobWeightMass, Pi.mul_apply, div_eq_mul_inv]
    rw [show
      (fun x => r x * (∫⁻ y, r y ∂μ)⁻¹ * v x) =
        (fun x => (r x * v x) * (∫⁻ y, r y ∂μ)⁻¹) by
          funext x
          ac_rfl]
    rw [lintegral_mul_const'' _ (hr.mul hv)]
  have hMassUnfolded :
      doobWeightMass (μ.withDensity (doobWeightedDensity μ r)) v =
        doobWeightMass μ (fun x => r x * v x) / doobWeightMass μ r := by
    simpa [doobWeightedMeasure] using hMass
  unfold doobWeightedMeasure
  rw [← withDensity_mul₀ hRawDensityMeas hOuterDensityMeas]
  apply withDensity_congr_ae
  filter_upwards with x
  simp only [Pi.mul_apply, doobWeightedDensity]
  rw [hMassUnfolded]
  simp only [div_eq_mul_inv]
  rw [ENNReal.inv_div (Or.inl hMassRTop) (Or.inl hMassRZero)]
  simp only [div_eq_mul_inv]
  calc
    r x * (doobWeightMass μ r)⁻¹ *
        (v x * (doobWeightMass μ r *
          (doobWeightMass μ (fun y => r y * v y))⁻¹)) =
      (r x * v x) *
        ((doobWeightMass μ r)⁻¹ * doobWeightMass μ r) *
          (doobWeightMass μ (fun y => r y * v y))⁻¹ := by
      ac_rfl
    _ = (r x * v x) *
        (doobWeightMass μ (fun y => r y * v y))⁻¹ := by
      rw [ENNReal.inv_mul_cancel hMassRZero hMassRTop, mul_one]

end

end MathlibAnalytic
end MGAP4D
