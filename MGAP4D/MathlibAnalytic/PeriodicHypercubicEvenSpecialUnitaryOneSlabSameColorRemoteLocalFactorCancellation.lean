import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalFactorBounds
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSixColorPlaquetteSeparation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Distinct right-boundary spatial links in one six-color class do not
interact in the exact target-local Boltzmann factor of the one-slab Wilson
kernel.

This is a raw-kernel statement.  It does not assert the corresponding
continuous-vacuum weight is independent of the remote source after integration
against the top eigenvector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_sameColor_remote_update_eq
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hColor : periodicHypercubicEvenSpatialSliceLinkColor H target =
      periodicHypercubicEvenSpatialSliceLinkColor H source)
    (hne : target ≠ source)
    (h k g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A (Function.update B source h) target g =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A (Function.update B source k) target g := by
  simp [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor,
    hne]

end

end MathlibAnalytic
end MGAP4D
