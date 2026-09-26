import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairCurrentValueDependentOuterSchurInterface
import Mathlib.Tactic

/-!
# Off-diagonal current-value interface to the outer transpose Schur receiver

The concrete target-law response is definitionally zero on the diagonal and
the physical influence envelope has zero diagonal.  Therefore the target-state
RMS majorant required by PR #4826 is needed only for genuine off-diagonal
source/target pairs.

This file removes the unnecessary diagonal RMS obligation while preserving the
same current-value source-pair carrier, exact decomposition, localPart, and
actual background-dependent coefficient K_A(target,source).

No new estimate, coefficient, factor two, or finite-cardinality factor is
introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

local instance currentValueOffDiagonalOuterSchurSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance currentValueOffDiagonalOuterSchurSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Current-value outer Schur interface requiring the RMS-to-state majorant
only off the response diagonal. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCurrentValue_aeOuterLIntegralTransposeSchurReceiver_of_decomposition_and_offDiagonalSecondMeanRMSMajorant
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
          target ≠ source →
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
    by_cases hEq : target = source
    · subst target
      have hDiag :
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A).influence source source = 0 :=
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A).influence_diagonal_zero source
      simpa [response, hDiag] using hBase
    · have hK0 :
          0 ≤
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
              H N hN beta hbeta A).influence target source :=
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A).influence_nonneg target source
      exact hBase.trans
        (mul_le_mul_of_nonneg_left (hRMS source target hEq) hK0)
  have hSchur :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStage_aeDependentNormedResponse_outerLIntegralTransposeSchurReceiver
      N hN s hs beta hbeta hcut H μ E
      state localPart response localProfile
      (by simpa [μ, E, localPart, response] using hDecomp)
      hLocal hResponse
  simpa [μ, E, localPart, response, localProfile] using hSchur

end

end MGAP4D.MathlibAnalytic
