import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkWeightFactorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalFactorBounds
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The literal ground-state one-link fiber weight factors through the exact
volume-independent target-local Boltzmann factor.

This is the carrier-explicit bridge between the ground-state one-link
fiber/disintegration layer and the target-local one-slab kernel layer. It
isolates the remaining target-coordinate dependence outside the controlled
local factor in the updated-right vacuum representative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight_eq_transferNorm_vacuum_localFactor_kernel_vacuum
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight
        H N hN beta hbeta left right target g =
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H N hN beta hbeta‖⁻¹ *
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
              H N hN beta hbeta).1 left *
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta left right target g *
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
                H N beta left right) *
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
              H N hN beta hbeta).1 (Function.update right target g))) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkFiberWeight_eq_transferNorm_vacuum_kernel_vacuum,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul]

end

end MathlibAnalytic
end MGAP4D
