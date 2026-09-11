import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetActionVariation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Updating one right-boundary spatial link changes the temporal-gauge crossing
action by exactly the Wilson energy difference at that same link.  All other
link contributions cancel. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_update_right_sub_eq
    (H N : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A
        (Function.update B target g) -
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A B =
    specialUnitaryWilsonPlaquetteEnergy N ((A target)⁻¹ * g) -
      specialUnitaryWilsonPlaquetteEnergy N ((A target)⁻¹ * B target) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction

end

end MathlibAnalytic
end MGAP4D
