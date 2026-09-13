import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumSameColorIntegralNormalForm
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalFactorBounds
import MGAP4D.MathlibAnalytic.RealIntegralCrossRatioCovarianceLocalization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- RED specification: the same-color remote four-point defect of the scaled
physical continuous-vacuum representative is exactly the unnormalized weighted
covariance numerator, under the reference left-boundary weight built from the
second target value and second source value, of the target-local ratio and the
source-conditioned one-slab-kernel ratio.

No distance-decay estimate is asserted here.  This theorem only performs the
exact algebraic localization needed before a genuine mixing/covariance bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_sameColor_remote_crossRatio_defect_eq_weightedCovarianceNumerator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hColor : periodicHypercubicEvenSpatialSliceLinkColor H target =
      periodicHypercubicEvenSpatialSliceLinkColor H source)
    (hne : target ≠ source)
    (h k g₁ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source h) target g₁)) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₂)) -
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₁)) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta
          (Function.update (Function.update B source h) target g₂)) =
      realIntegralWeightedCovarianceNumerator
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
        (fun A =>
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
              H N hN beta hbeta).1 A *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₂ *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta A (Function.update B source k))
        (fun A =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₁ /
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₂)
        (fun A =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta A (Function.update B source h) /
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta A (Function.update B source k)) := by
  rfl

end

end MathlibAnalytic
end MGAP4D
