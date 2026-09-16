import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumKernelHarnack
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberRemoteSlabCancellation
import MGAP4D.MathlibAnalytic.RealIntegralCrossRatioCovarianceLocalization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance physicalContinuousVacuumRemoteNoShareSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

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

/-- For any two distinct spatial links sharing no Wilson plaquette, the remote
four-point defect of the scaled physical continuous-vacuum representative is
exactly the unnormalized weighted covariance numerator of the target-local
update ratio and the source-conditioned one-slab-kernel ratio.

Unlike the earlier same-color theorem, this statement uses only the literal
geometric noninteraction hypothesis.  It still makes no spatial decay,
independence, Gibbs-identification, or Doob `K = 1` claim for the integrated
continuous vacuum. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_remote_noShare_crossRatio_defect_eq_weightedCovarianceNumerator
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
  have h11 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_remote_noShare_integral_normal_form
      H N hN beta hbeta B (target := target) (source := source) hne hNoShare h g₁
  have h22 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_remote_noShare_integral_normal_form
      H N hN beta hbeta B (target := target) (source := source) hne hNoShare k g₂
  have h12 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_remote_noShare_integral_normal_form
      H N hN beta hbeta B (target := target) (source := source) hne hNoShare k g₁
  have h21 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_remote_noShare_integral_normal_form
      H N hN beta hbeta B (target := target) (source := source) hne hNoShare h g₂
  rw [h11, h22, h12, h21]
  have hq :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B target g₂ ≠ 0 := by
    intro A
    exact ne_of_gt
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
        H N beta A B target g₂)
  have hs :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A (Function.update B source k) ≠ 0 := by
    intro A
    exact ne_of_gt
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H N beta A (Function.update B source k))
  simpa [mul_assoc] using
    (real_integral_crossRatio_defect_eq_weightedCovarianceNumerator
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      (fun A =>
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN beta hbeta).1 A)
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target g₁)
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target g₂)
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A (Function.update B source h))
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A (Function.update B source k))
      hq hs)

/-- Outside the literal Wilson interaction neighborhood, the same remote
four-point defect is an explicit source spatial-half-update ratio times a
weighted covariance numerator of two one-link observables on the left
boundary: the target local-factor ratio and the source Wilson crossing ratio.

This isolates the remaining long-range obstruction to the canonical vacuum
weight itself.  No summability or decay estimate is asserted. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_remote_noShare_crossRatio_defect_eq_sourceSpatialRatio_mul_weightedCovarianceNumerator_sourceCrossingRatio
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
          specialUnitaryWilsonRelativeKernel N beta (A source) h /
            specialUnitaryWilsonRelativeKernel N beta (A source) k) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_remote_noShare_crossRatio_defect_eq_weightedCovarianceNumerator
      H N hN beta hbeta B (target := target) (source := source)
      hne hNoShare h k g₁ g₂]
  have hSourceRatio :
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
              (Function.update B source h) /
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
              (Function.update B source k)) =
        (fun A =>
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
              H N beta B source h /
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
              H N beta B source k) *
          (specialUnitaryWilsonRelativeKernel N beta (A source) h /
            specialUnitaryWilsonRelativeKernel N beta (A source) k)) := by
    funext A
    have hpair :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_source_update_pairwise_likelihoodRatio
        H N beta A B source h k
    have hQk :
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta A
            (Function.update B source k) ≠ 0 := by
      exact ne_of_gt
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
          H N beta A (Function.update B source k))
    have hSk :
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
            H N beta B source k ≠ 0 := by
      exact ne_of_gt
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor_pos
          H N beta B source k)
    have hrk : specialUnitaryWilsonRelativeKernel N beta (A source) k ≠ 0 := by
      unfold specialUnitaryWilsonRelativeKernel
      unfold specialUnitaryWilsonBoltzmannCentralFunction
      exact ne_of_gt (Real.exp_pos _)
    field_simp [hQk, hSk, hrk] <;> nlinarith [hpair]
  rw [hSourceRatio]
  exact
    realIntegralWeightedCovarianceNumerator_const_mul_right
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
        specialUnitaryWilsonRelativeKernel N beta (A source) h /
          specialUnitaryWilsonRelativeKernel N beta (A source) k)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B source h /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetSpatialHalfUpdateFactor
          H N beta B source k)

end

end MathlibAnalytic
end MGAP4D
