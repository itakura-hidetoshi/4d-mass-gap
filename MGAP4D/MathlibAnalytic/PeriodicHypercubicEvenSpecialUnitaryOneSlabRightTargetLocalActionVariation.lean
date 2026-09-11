import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryCrossingRightTargetLinkEnergyVariation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitarySpatialTargetLinkEnergyVariation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A right-boundary target-link update changes the complete one-slab action by
the target crossing-energy difference plus one half of the sum of spatial
Wilson-energy differences over intrinsic plaquettes touching the target.  This
is an exact composition theorem; no quantitative estimate is asserted here. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_update_right_sub_eq_targetLocal
    (H N : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A
        (Function.update B target g) -
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A B =
    (specialUnitaryWilsonPlaquetteEnergy N ((A target)⁻¹ * g) -
      specialUnitaryWilsonPlaquetteEnergy N ((A target)⁻¹ * B target)) +
    (1 / 2 : ℝ) *
      ∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
        (specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
              (Function.update B target g) p) -
          specialUnitaryWilsonPlaquetteEnergy N
            (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B p)) := by
  calc
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A
          (Function.update B target g) -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H N A B =
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A
          (Function.update B target g) -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H N A B) +
      (1 / 2 : ℝ) *
        (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
            (Function.update B target g) -
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N B) :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_update_right_sub_eq
        H N A B target g
    _ =
      (specialUnitaryWilsonPlaquetteEnergy N ((A target)⁻¹ * g) -
        specialUnitaryWilsonPlaquetteEnergy N ((A target)⁻¹ * B target)) +
      (1 / 2 : ℝ) *
        (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
            (Function.update B target g) -
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N B) := by
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_update_right_sub_eq]
    _ =
      (specialUnitaryWilsonPlaquetteEnergy N ((A target)⁻¹ * g) -
        specialUnitaryWilsonPlaquetteEnergy N ((A target)⁻¹ * B target)) +
      (1 / 2 : ℝ) *
        ∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
          (specialUnitaryWilsonPlaquetteEnergy N
              (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
                (Function.update B target g) p) -
            specialUnitaryWilsonPlaquetteEnergy N
              (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B p)) := by
      rw [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_update_sub_eq_targetTouching]

end

end MathlibAnalytic
end MGAP4D
