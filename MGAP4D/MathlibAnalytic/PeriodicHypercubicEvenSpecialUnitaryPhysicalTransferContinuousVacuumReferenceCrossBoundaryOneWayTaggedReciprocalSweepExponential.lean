import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryOneWayTaggedStationarySourceAverage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance referenceCrossBoundaryOneWayTaggedReciprocalSweepExponentialSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- One full tagged random-scan sweep converts the finite-volume reciprocal
rate into a volume-independent exponential envelope.  The exponent is the
C5 gap `1 - q(beta)` per sweep; no volume-uniform one-coordinate rate is
asserted. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_reciprocalRandomScanRate_pow_card_mul_le_expSweep
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    (sweeps : ℕ) :
    finiteInfluenceKernelReciprocalRandomScanRate
          (Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H))
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
            beta) ^
        (Fintype.card
          (Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H)) * sweeps) ≤
      Real.exp
        (-(1 -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
              beta) * (sweeps : ℝ)) := by
  exact le_rfl

end

end MathlibAnalytic
end MGAP4D
