import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumKernelHarnack
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberRemoteSlabCancellation
import MGAP4D.MathlibAnalytic.RealIntegralCrossRatioCovarianceLocalization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Exact integral normal form for a continuous-vacuum value after changing a
geometrically remote source link and then fixing the target value.  The
hypothesis is the literal Wilson condition that the two links share no spatial
plaquette; no six-color coincidence is assumed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_remote_noShare_integral_normal_form
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (h g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta
        (Function.update (Function.update B source h) target g) =
      ∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta).1 A *
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g *
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta A (Function.update B source h))
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_topNorm_mul_eq_integral_kernel]
  apply integral_congr_ae
  filter_upwards with A
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_update_right_eq_localFactor_mul]
  rw [
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_update_rightBase_remote
      H N beta A B target source h g (Ne.symm hne) hNoShare]

end

end MathlibAnalytic
end MGAP4D
