import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetActionVariation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

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
  classical
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
  calc
    ((periodicHypercubicEvenSpatialSliceLinkList H).map fun e =>
        specialUnitaryWilsonPlaquetteEnergy N
          ((A e)⁻¹ * Function.update B target g e)).sum -
        ((periodicHypercubicEvenSpatialSliceLinkList H).map fun e =>
          specialUnitaryWilsonPlaquetteEnergy N ((A e)⁻¹ * B e)).sum =
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        specialUnitaryWilsonPlaquetteEnergy N
          ((A e)⁻¹ * Function.update B target g e)) -
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        specialUnitaryWilsonPlaquetteEnergy N ((A e)⁻¹ * B e) := by
      simp [periodicHypercubicEvenSpatialSliceLinkList]
    _ = ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        (specialUnitaryWilsonPlaquetteEnergy N
            ((A e)⁻¹ * Function.update B target g e) -
          specialUnitaryWilsonPlaquetteEnergy N ((A e)⁻¹ * B e)) := by
      rw [← Finset.sum_sub_distrib]
    _ = specialUnitaryWilsonPlaquetteEnergy N ((A target)⁻¹ * g) -
        specialUnitaryWilsonPlaquetteEnergy N ((A target)⁻¹ * B target) := by
      rw [Finset.sum_eq_single target]
      · simp
      · intro e _he hne
        simp [hne]
      · simp

end

end MathlibAnalytic
end MGAP4D
