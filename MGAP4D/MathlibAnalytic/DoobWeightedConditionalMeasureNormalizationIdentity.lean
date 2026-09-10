import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkAENormalizedFiberProbability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

example
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
  rfl

end

end MathlibAnalytic
end MGAP4D
