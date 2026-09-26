import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageAEDependentNormedResponseOuterLIntegralSchurReceiver
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairCurrentValueFixedBackgroundFiberL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairCurrentValueLocalPartTargetResidual
import Mathlib.Tactic

/-!
# Current-value source-pair interface to the outer transpose Schur receiver

PRs #4822--#4825 place the concrete target-law responses, the final
second-law-mean RMS amplitudes, and the diagonal localPart in one
source-dependent fixed-background L2 carrier

  E(C,A,source).

PR #4823 allows the dependent-response assembly data to hold only almost
everywhere in the outer background.

This file composes those concrete pieces.  For one fixed vacuum-side
configuration C it assumes only the two genuinely remaining observable-specific
interfaces:

1. the exact finite decomposition
     state = localPart + sum_target response;
2. the source-independent target-state majorization
     ||RMS2(C,A,source,target)|| <= ||state(C,A,target)||.

The response estimate itself is discharged by PR #4822 with the actual
background-dependent physical envelope K_A(target,source).  The localPart
bound is exact by PR #4824.

No pin-free replacement, response coefficient, factor two, or
finite-cardinality factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

local instance currentValueDependentOuterSchurSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance currentValueDependentOuterSchurSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Concrete current-value source-pair data feed the a.e. outer transpose
Schur receiver once the exact state decomposition and the target-state RMS
majorant are supplied.

The matrix orientation remains exactly K_A(target,source). -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCurrentValue_aeOuterLIntegralTransposeSchurReceiver_of_decomposition_and_secondMeanRMSMajorant
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
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (state :
      ∀ A source,
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointCurrentValueFixedBackgroundSourcePairL2
          H N hN beta hbeta C A distinguishedSource source)
    (hDecomp :
      ∀ᵐ A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C,
        ∀ source,
          state A source =
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2
                H N hN beta hbeta C A distinguishedSource source F +
              ∑ target,
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseCurrentValueFixedBackgroundL2
                  H N hN beta hbeta C A distinguishedSource source target
                  F hF bound hbound C)
    (hRMSMajorant :
      ∀ᵐ A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C,
        ∀ source target,
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeCurrentValueFixedBackgroundL2
              H N hN beta hbeta C A distinguishedSource source target
              F hF bound hbound C‖ ≤
            ‖state A target‖) :
    (∫⁻ A, ENNReal.ofReal
      ((1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
          s beta) ^ 2 *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, ‖state A e‖ ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C) ≤
      ∫⁻ A, ENNReal.ofReal
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalMean
            H N hN beta hbeta C A distinguishedSource e F| ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta C
  let E :=
    fun A source =>
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointCurrentValueFixedBackgroundSourcePairL2
        H N hN beta hbeta C A distinguishedSource source
  let localPart :=
    fun A source =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2
        H N hN beta hbeta C A distinguishedSource source F
  let response :=
    fun A source target =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseCurrentValueFixedBackgroundL2
        H N hN beta hbeta C A distinguishedSource source target
        F hF bound hbound C
  let localProfile :=
    fun A source =>
      |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalMean
        H N hN beta hbeta C A distinguishedSource source F|
  have hLocal :
      ∀ᵐ A ∂μ, ∀ source,
        ‖localPart A source‖ ≤ localProfile A source := by
    filter_upwards with A
    intro source
    have hEq :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2_norm_eq_abs
        H N hN beta hbeta C A distinguishedSource source F
    simpa [localPart, localProfile] using hEq.le
  have hResponse :
      ∀ᵐ A ∂μ, ∀ source target,
        ‖response A source target‖ ≤
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A).influence target source *
            ‖state A target‖ := by
    filter_upwards [hRMSMajorant] with A hRMS
    intro source target
    have hBase :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseCurrentValueFixedBackgroundL2_norm_le_physicalEnvelope_mul_secondMeanRMSAmplitudeCurrentValueFixedBackgroundL2_norm
        N hN s hs beta hbeta hcut H C A distinguishedSource source target
        F hF bound hbound C
    have hK0 :
        0 ≤
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A).influence target source :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A).influence_nonneg target source
    exact hBase.trans
      (mul_le_mul_of_nonneg_left (hRMS source target) hK0)
  have hSchur :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStage_aeDependentNormedResponse_outerLIntegralTransposeSchurReceiver
      N hN s hs beta hbeta hcut H μ E
      state localPart response localProfile
      (by simpa [μ, E, localPart, response] using hDecomp)
      hLocal hResponse
  simpa [μ, E, localPart, response, localProfile] using hSchur

end

end MGAP4D.MathlibAnalytic
