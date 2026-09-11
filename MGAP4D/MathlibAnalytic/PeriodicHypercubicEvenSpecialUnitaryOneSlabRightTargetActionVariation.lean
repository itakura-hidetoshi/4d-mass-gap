import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabKernel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Updating one link on the right boundary changes the complete temporal-gauge
one-slab Wilson action only through the crossing action and the right spatial
half-action.  This is an exact algebraic bridge; no locality estimate or
quantitative bound is asserted here. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_update_right_sub_eq
    (H N : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A
        (Function.update B target g) -
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A B =
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A
        (Function.update B target g) -
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A B) +
    (1 / 2 : ℝ) *
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
          (Function.update B target g) -
        periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N B) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction

end

end MathlibAnalytic
end MGAP4D
