import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateKernelSectionProbability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance physicalContinuousVacuumRemoteNoShareProbabilityCovarianceSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- For a geometrically remote target/source pair, the exact scaled
continuous-vacuum four-point defect is a source spatial factor times the
squared mass of one fixed-right ground-state kernel section times an ordinary
covariance under the normalized kernel-section probability law.

This converts the remaining remote obstruction from an unnormalized weighted
covariance numerator into a genuine probability covariance.  It does not
identify that probability law with a regular conditional distribution or with
the bare Wilson Gibbs measure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_remote_noShare_crossRatio_defect_eq_sourceSpatialRatio_mul_mass_sq_mul_probabilityCovariance
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
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
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B source h /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B source k) *
      ((‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H N hN beta hbeta‖ *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂)) ^ 2 *
        realIntegralCovariance
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂))
          (fun A =>
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target g₁ /
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target g₂)
          (fun A =>
            specialUnitaryWilsonRelativeKernel N beta (A source) h /
              specialUnitaryWilsonRelativeKernel N beta (A source) k)) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_remote_noShare_crossRatio_defect_eq_sourceSpatialRatio_mul_weightedCovarianceNumerator_sourceCrossingRatio
      H N hN beta hbeta B (target := target) (source := source)
      hne hNoShare h k g₁ g₂]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_remote_noShare_weightedCovarianceNumerator_eq_groundStateKernelSection
      H N hN beta hbeta B (target := target) (source := source)
      hne hNoShare k g₂]
  change
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B source h /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B source k) *
      realIntegralWeightedCovarianceNumerator
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionWeight
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₂))
        (fun A =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₁ /
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₂)
        (fun A =>
          specialUnitaryWilsonRelativeKernel N beta (A source) h /
            specialUnitaryWilsonRelativeKernel N beta (A source) k) = _
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSection_weightedCovarianceNumerator_eq_mass_sq_mul_probabilityCovariance
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g₂)]

end

end MathlibAnalytic
end MGAP4D
