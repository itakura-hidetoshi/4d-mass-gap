import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairLinkIndexedCanonicalAssembledState
import Mathlib.Tactic

/-!
# Current-value target RMS max profile

The remaining interface after PR #4829 is still quantified over both source
and target:

  ||RMS2(F_target; C,A,source,target)||
    <= ||assembledState(C,A,target)||.

For fixed `C`, `A`, and `target`, all source links form a finite set.
This file packages their RMS norms into one target-indexed scalar profile by
taking the finite maximum (with an explicit zero inserted so the defining
finset is nonempty):

  rmsProfile(C,A,target)
    = max(0, max_source ||RMS2(C,A,source,target)||).

Therefore every source RMS is bounded by exactly the same target profile with
coefficient one.  The pairwise RMS-to-state premise is equivalent, for the
outer-Schur application, to the single target-profile inequality

  rmsProfile(C,A,target) <= ||assembledState(C,A,target)||.

No finite sum, Cauchy--Schwarz step, volume factor, response coefficient,
pin-free replacement, or factor two is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

local instance currentValueTargetRMSMaxProfileSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance currentValueTargetRMSMaxProfileSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Finite set consisting of zero and all source-indexed fixed-background
second-mean RMS norms for one target. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCurrentValueTargetRMSNormValues
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      PeriodicHypercubicEvenSpatialSliceLink H →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : ∀ e, StronglyMeasurable (F e))
    (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hbound : ∀ e z, ‖F e z‖ ≤ bound e) :
    Finset ℝ :=
  insert 0 <|
    (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)).image
      (fun source =>
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeCurrentValueFixedBackgroundL2
            H N hN beta hbeta C A distinguishedSource source target
            (F target) (hF target) (bound target) (hbound target) C‖)

/-- Source-uniform target RMS profile at one fixed current-value background. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCurrentValueTargetRMSMaxProfile
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      PeriodicHypercubicEvenSpatialSliceLink H →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : ∀ e, StronglyMeasurable (F e))
    (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hbound : ∀ e z, ‖F e z‖ ≤ bound e) : ℝ :=
  let values :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCurrentValueTargetRMSNormValues
      H N hN beta hbeta C A distinguishedSource target F hF bound hbound
  values.max' (by
    dsimp [values,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCurrentValueTargetRMSNormValues]
    simp)

/-- Every source-indexed fixed-background second-mean RMS norm is bounded by
the target max profile with coefficient one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeCurrentValueFixedBackgroundL2_norm_le_targetRMSMaxProfile
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      PeriodicHypercubicEvenSpatialSliceLink H →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : ∀ e, StronglyMeasurable (F e))
    (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hbound : ∀ e z, ‖F e z‖ ≤ bound e) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeCurrentValueFixedBackgroundL2
        H N hN beta hbeta C A distinguishedSource source target
        (F target) (hF target) (bound target) (hbound target) C‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCurrentValueTargetRMSMaxProfile
        H N hN beta hbeta C A distinguishedSource target
        F hF bound hbound := by
  let values :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCurrentValueTargetRMSNormValues
      H N hN beta hbeta C A distinguishedSource target F hF bound hbound
  have hMem :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeCurrentValueFixedBackgroundL2
          H N hN beta hbeta C A distinguishedSource source target
          (F target) (hF target) (bound target) (hbound target) C‖ ∈ values := by
    dsimp [values,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCurrentValueTargetRMSNormValues]
    simp
  change
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeCurrentValueFixedBackgroundL2
        H N hN beta hbeta C A distinguishedSource source target
        (F target) (hF target) (bound target) (hbound target) C‖ ≤
      values.max' _
  exact Finset.le_max' values _ hMem

/-- The max profile is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCurrentValueTargetRMSMaxProfile_nonneg
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      PeriodicHypercubicEvenSpatialSliceLink H →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : ∀ e, StronglyMeasurable (F e))
    (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hbound : ∀ e z, ‖F e z‖ ≤ bound e) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCurrentValueTargetRMSMaxProfile
        H N hN beta hbeta C A distinguishedSource target
        F hF bound hbound := by
  let values :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCurrentValueTargetRMSNormValues
      H N hN beta hbeta C A distinguishedSource target F hF bound hbound
  have hMem : (0 : ℝ) ∈ values := by
    dsimp [values,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCurrentValueTargetRMSNormValues]
    simp
  change 0 ≤ values.max' _
  exact Finset.le_max' values 0 hMem

/-- Every current-value target-law response is bounded by the actual physical
envelope times the source-uniform target RMS profile. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseCurrentValueFixedBackgroundL2_norm_le_physicalEnvelope_mul_targetRMSMaxProfile
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      PeriodicHypercubicEvenSpatialSliceLink H →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : ∀ e, StronglyMeasurable (F e))
    (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hbound : ∀ e z, ‖F e z‖ ≤ bound e) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseCurrentValueFixedBackgroundL2
        H N hN beta hbeta C A distinguishedSource source target
        (F target) (hF target) (bound target) (hbound target) C‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A).influence target source *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCurrentValueTargetRMSMaxProfile
        H N hN beta hbeta C A distinguishedSource target
        F hF bound hbound := by
  have hBase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseCurrentValueFixedBackgroundL2_norm_le_physicalEnvelope_mul_secondMeanRMSAmplitudeCurrentValueFixedBackgroundL2_norm
      N hN s hs beta hbeta hcut H C A distinguishedSource source target
      (F target) (hF target) (bound target) (hbound target) C
  have hRMS :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeCurrentValueFixedBackgroundL2_norm_le_targetRMSMaxProfile
      H N hN beta hbeta C A distinguishedSource source target
      F hF bound hbound
  have hK0 :
      0 ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A).influence target source :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
      H N hN beta hbeta A).influence_nonneg target source
  exact hBase.trans (mul_le_mul_of_nonneg_left hRMS hK0)

/-- The link-indexed outer-Schur theorem now needs only one target-indexed
profile-to-state inequality, rather than a separate RMS inequality for every
source/target pair. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedCanonicalAssembledCurrentValue_aeOuterLIntegralTransposeSchurReceiver_of_targetRMSMaxProfile_le_state
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      PeriodicHypercubicEvenSpatialSliceLink H →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : ∀ e, StronglyMeasurable (F e))
    (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hbound : ∀ e z, ‖F e z‖ ≤ bound e)
    (hProfile :
      ∀ᵐ A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C,
        ∀ target,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCurrentValueTargetRMSMaxProfile
              H N hN beta hbeta C A distinguishedSource target
              F hF bound hbound ≤
            ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedCanonicalAssembledCurrentValueFixedBackgroundL2
              H N hN beta hbeta C A distinguishedSource target
              F hF bound hbound‖) :
    (∫⁻ A, ENNReal.ofReal
      ((1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
          s beta) ^ 2 *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedCanonicalAssembledCurrentValueFixedBackgroundL2
            H N hN beta hbeta C A distinguishedSource e
            F hF bound hbound‖ ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C) ≤
      ∫⁻ A, ENNReal.ofReal
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalMean
            H N hN beta hbeta C A distinguishedSource e (F e)| ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedCanonicalAssembledCurrentValue_aeOuterLIntegralTransposeSchurReceiver_of_offDiagonalSecondMeanRMSMajorant
      N hN s hs beta hbeta hcut H C distinguishedSource
      F hF bound hbound
  filter_upwards [hProfile] with A hProfileA
  intro source target hne
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeCurrentValueFixedBackgroundL2_norm_le_targetRMSMaxProfile
      H N hN beta hbeta C A distinguishedSource source target
      F hF bound hbound).trans
      (hProfileA target)

end

end MGAP4D.MathlibAnalytic
