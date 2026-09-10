import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkAENormalizedFiberProbability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Multiplying expectation against a normalized Doob weighted measure by its
normalizing mass recovers the corresponding unnormalized weighted integral.

The nonzero and finite mass receipts are explicit: no cancellation is performed
at a zero or infinite normalization mass. -/
theorem doobWeightMass_mul_lintegral_doobWeightedMeasure
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    (w g : α → ENNReal)
    (hw : AEMeasurable w μ)
    (hg : AEMeasurable g μ)
    (hMassZero : doobWeightMass μ w ≠ 0)
    (hMassTop : doobWeightMass μ w ≠ ∞) :
    doobWeightMass μ w * (∫⁻ x, g x ∂doobWeightedMeasure μ w) =
      ∫⁻ x, w x * g x ∂μ := by
  change doobWeightMass μ w *
      (∫⁻ x, g x ∂μ.withDensity (fun x => w x / doobWeightMass μ w)) =
    ∫⁻ x, w x * g x ∂μ
  rw [lintegral_withDensity_eq_lintegral_mul₀ (hw.div_const _) hg]
  simp only [Pi.mul_apply, div_eq_mul_inv]
  rw [show
    (fun x => w x * (doobWeightMass μ w)⁻¹ * g x) =
      (fun x => (w x * g x) * (doobWeightMass μ w)⁻¹) by
        funext x
        ac_rfl]
  rw [lintegral_mul_const'' _ (hw.mul hg)]
  calc
    doobWeightMass μ w *
        ((∫⁻ x, w x * g x ∂μ) * (doobWeightMass μ w)⁻¹) =
      (∫⁻ x, w x * g x ∂μ) *
        (doobWeightMass μ w * (doobWeightMass μ w)⁻¹) := by
      ac_rfl
    _ = ∫⁻ x, w x * g x ∂μ := by
      rw [ENNReal.mul_inv_cancel hMassZero hMassTop, mul_one]

end

end MathlibAnalytic
end MGAP4D
