import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryCrossingRightTargetLinkEnergyVariation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitarySpatialTargetLinkEnergyVariation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- RED specification: a right-boundary target-link update changes the complete
one-slab action by the target crossing-energy difference plus one half of the
sum of spatial Wilson-energy differences over intrinsic plaquettes touching the
target.  No quantitative estimate is asserted here. -/
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
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_update_right_sub_eq]

end

end MathlibAnalytic
end MGAP4D
