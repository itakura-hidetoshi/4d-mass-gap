import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumLocalHarnack
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Updating one intrinsic spatial target link changes the spatial Wilson action
by exactly the sum of Wilson-energy differences over intrinsic spatial
plaquettes touching that target. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_update_sub_eq_targetTouching
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
        (Function.update A target g) -
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N A =
    ∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
      (specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
            (Function.update A target g) p) -
        specialUnitaryWilsonPlaquetteEnergy N
          (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p)) := by
  classical
  rw [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_eq_finset_sum,
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_eq_finset_sum,
    ← Finset.sum_sub_distrib]

end

end MathlibAnalytic
end MGAP4D
