import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateOneLinkNormalizedMinorization

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

example
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (ENNReal.ofReal (Real.exp (16 * beta)))⁻¹ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberDensity
        H N hN beta hbeta left right target g := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberDensity_lower_bound
      H N hN beta hbeta left right target g

end

end MathlibAnalytic
end MGAP4D
