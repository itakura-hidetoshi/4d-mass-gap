import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalActionVariation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- RED specification: updating one right-boundary target link multiplies the
complete one-slab Wilson kernel by the exact Boltzmann factor of the already
localized target-link action increment.  No division, normalization, or
quantitative estimate is asserted here. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_targetLocalFactor
    (H N : ℕ)
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
        (Function.update B target g) =
    Real.exp
        (-beta *
          ((specialUnitaryWilsonPlaquetteEnergy N ((A target)⁻¹ * g) -
              specialUnitaryWilsonPlaquetteEnergy N ((A target)⁻¹ * B target)) +
            (1 / 2 : ℝ) *
              ∑ p ∈ periodicHypercubicEvenSpatialSliceTouchingPlaquettes H target,
                (specialUnitaryWilsonPlaquetteEnergy N
                    (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
                      (Function.update B target g) p) -
                  specialUnitaryWilsonPlaquetteEnergy N
                    (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B p)))) *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A B := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]

end

end MathlibAnalytic
end MGAP4D
