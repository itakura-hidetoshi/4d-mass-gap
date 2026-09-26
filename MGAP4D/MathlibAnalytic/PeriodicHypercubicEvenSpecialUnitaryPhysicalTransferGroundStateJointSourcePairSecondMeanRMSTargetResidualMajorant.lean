import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairSecondMeanRMSUniformFeedback
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferDiagonalUpdatedVarianceGenuineResidual
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferDiagonalProjectionKernelSectionIntegral
import Mathlib.Tactic

/-!
# Source-independent target residual majorant for the second-mean RMS energy

PR #4812 gives a uniform absorbed RMS estimate whose right-hand side is still
written as the stationarity-returned updated reference variance for a chosen
source link.

At diagonal current-value parameters, PR #4798 already identifies that updated
variance with a fixed-right kernel-section target fluctuation.  The diagonal
fluctuation formula from PR #4760 removes the remaining source parameter
literally:

  F(C,A) - integral_g F(C,A[target <- g]) d kappa_{C,A,target}.

This file packages that source-independent quantity as a target residual energy

  TargetKernelSectionResidualEnergy(C,target,F),

proves every diagonal source-reference updated variance is exactly this same
quantity, and rewrites the PR #4812 RMS estimate as

  uniformGap * ofReal(||RMS2(C,source,target)||^2)
    <= (K_H(beta)+1) * TargetKernelSectionResidualEnergy(C,target,F).

The right-hand side now depends on target but not on source, distinguished
source, or source-fiber current values.

No new cutoff, response coefficient, Harnack factor, factor two, or
cardinality loss is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance secondMeanRMSTargetResidualMajorantSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance secondMeanRMSTargetResidualMajorantSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance secondMeanRMSTargetResidualMajorantSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance secondMeanRMSTargetResidualMajorantSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance secondMeanRMSTargetResidualMajorantSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance secondMeanRMSTargetResidualMajorantSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Fixed-boundary target residual energy under the genuine fixed-right
kernel-section law.  This quantity is indexed by the resampled target only;
there is no source-link parameter. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) : ℝ≥0∞ :=
  ∫⁻ A,
    ENNReal.ofReal
      ((F (C, A) -
          ∫ g,
            F (C, Function.update A target g)
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
              H N hN beta hbeta C A target) ^ 2)
    ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta C

/-- At diagonal current values, the stationarity-returned updated reference
variance is exactly the source-independent target kernel-section residual
energy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_referenceUpdatedBackgroundVarianceEnergy_diagonal_lintegral_eq_targetKernelSectionResidualEnergy
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ A,
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
          H N hN beta hbeta C distinguishedSource source target
          (C distinguishedSource) (C source) F C A)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta C source distinguishedSource
        (C distinguishedSource) (C source)) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
        H N hN beta hbeta C target F := by
  let rightF :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun D => F (C, D)
  have hRightStrong : StronglyMeasurable rightF :=
    hF.comp_measurable (measurable_const.prodMk measurable_id)
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_referenceUpdatedBackgroundVarianceEnergy_diagonal_lintegral_eq_kernelSectionFluctuation_sq_lintegral
      H N hN beta hbeta C distinguishedSource source target
      F hF bound hbound]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
  apply lintegral_congr
  intro A
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRemoteKernelSectionOneLinkFluctuation_diagonal_eq_value_sub_kernelSectionSpatialLinkIntegral
      H N hN beta hbeta C A target source rightF hRightStrong]
  rfl

/-- Diagonal updated reference variance is exactly independent of the chosen
source link. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_referenceUpdatedBackgroundVarianceEnergy_diagonal_lintegral_source_independent
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source₁ source₂ target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ A,
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
          H N hN beta hbeta C distinguishedSource source₁ target
          (C distinguishedSource) (C source₁) F C A)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta C source₁ distinguishedSource
        (C distinguishedSource) (C source₁)) =
    (∫⁻ A,
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawUpdatedBackgroundVarianceEnergy
          H N hN beta hbeta C distinguishedSource source₂ target
          (C distinguishedSource) (C source₂) F C A)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta C source₂ distinguishedSource
        (C distinguishedSource) (C source₂)) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_referenceUpdatedBackgroundVarianceEnergy_diagonal_lintegral_eq_targetKernelSectionResidualEnergy
      H N hN beta hbeta C distinguishedSource source₁ target
      F hF bound hbound,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_referenceUpdatedBackgroundVarianceEnergy_diagonal_lintegral_eq_targetKernelSectionResidualEnergy
      H N hN beta hbeta C distinguishedSource source₂ target
      F hF bound hbound]

/-- Target-indexed form of the PR #4812 uniform absorbed RMS estimate.
At diagonal current values the majorant depends only on the target residual
energy, not on the source. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_diagonal_one_sub_halfBarrierPinFreeCoefficient_sq_ofReal_mul_secondMeanRMSAmplitudeL2_norm_sq_ofReal_le_harnackFactor_add_one_mul_targetKernelSectionResidualEnergy
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (1 -
        ENNReal.ofReal
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
            s beta) ^ 2)) *
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
            H N hN beta hbeta C distinguishedSource source target
            (C distinguishedSource) (C source)
            F hF bound hbound C‖ ^ 2) ≤
      (ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) + 1) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointTargetKernelSectionResidualEnergy
          H N hN beta hbeta C target F := by
  have hRMS :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_one_sub_halfBarrierPinFreeCoefficient_sq_ofReal_mul_secondMeanRMSAmplitudeL2_norm_sq_ofReal_le_harnackVariance
      N hN s hs beta hbeta hcut H C distinguishedSource source target hne
      (C distinguishedSource) (C source)
      F hF bound hbound C
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLaw_referenceUpdatedBackgroundVarianceEnergy_diagonal_lintegral_eq_targetKernelSectionResidualEnergy
      H N hN beta hbeta C distinguishedSource source target
      F hF bound hbound] at hRMS
  exact hRMS

end

end MGAP4D.MathlibAnalytic
