import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairCanonicalAssembledCurrentValueState
import Mathlib.Tactic

/-!
# Link-indexed canonical assembled current-value state

The final six-spatial sweep does not use one concrete representative for every
link.  PR #4770 supplies a bounded concrete representative at the canonical
sweep stage associated with each link.

Accordingly, the observable data must be link-indexed:

  F_e.

For a fixed source link, its localPart uses F_source.  The response indexed by
a target link uses F_target, because the physical response estimate has the
orientation

  K(target,source) * target-amplitude.

This file defines the canonical assembled state with exactly that orientation:

  state_source
    = localPart(F_source)
      + sum_target response(F_target; source,target).

Thus the source-dependent carrier remains the current-value pair fiber for the
source, while the observable entering each response is target-indexed.

The exact decomposition is definitional.  The sole nontrivial outer-Schur
interface remains the off-diagonal bound of each target RMS amplitude by the
norm of the assembled target state.

No new estimate, coefficient, factor two, pin-free replacement, or
finite-cardinality factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

local instance linkIndexedCanonicalAssembledStateSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance linkIndexedCanonicalAssembledStateSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Canonical assembled source state for a link-indexed family of bounded
concrete observables. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedCanonicalAssembledCurrentValueFixedBackgroundL2
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      PeriodicHypercubicEvenSpatialSliceLink H →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : ∀ e, StronglyMeasurable (F e))
    (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hbound : ∀ e z, ‖F e z‖ ≤ bound e) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointCurrentValueFixedBackgroundSourcePairL2
      H N hN beta hbeta C A distinguishedSource source :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2
      H N hN beta hbeta C A distinguishedSource source (F source) +
    ∑ target,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseCurrentValueFixedBackgroundL2
        H N hN beta hbeta C A distinguishedSource source target
        (F target) (hF target) (bound target) (hbound target) C

/-- Exact target-indexed response decomposition of the link-indexed assembled
state. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedCanonicalAssembledCurrentValueFixedBackgroundL2_eq_localPart_add_sum_targetResponse
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      PeriodicHypercubicEvenSpatialSliceLink H →
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : ∀ e, StronglyMeasurable (F e))
    (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hbound : ∀ e z, ‖F e z‖ ≤ bound e) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedCanonicalAssembledCurrentValueFixedBackgroundL2
        H N hN beta hbeta C A distinguishedSource source
        F hF bound hbound =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2
          H N hN beta hbeta C A distinguishedSource source (F source) +
        ∑ target,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseCurrentValueFixedBackgroundL2
            H N hN beta hbeta C A distinguishedSource source target
            (F target) (hF target) (bound target) (hbound target) C := by
  rfl

/-- Link-indexed concrete interface to the outer transpose Schur receiver.

The response indexed by target uses F_target, while the localPart indexed by
source uses F_source.  This matches the stagewise representative orientation
from PR #4770 and the matrix orientation K(target,source). -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedCanonicalAssembledCurrentValue_aeOuterLIntegralTransposeSchurReceiver_of_offDiagonalSecondMeanRMSMajorant
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
    (hRMSMajorant :
      ∀ᵐ A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C,
        ∀ source target,
          target ≠ source →
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeCurrentValueFixedBackgroundL2
              H N hN beta hbeta C A distinguishedSource source target
              (F target) (hF target) (bound target) (hbound target) C‖ ≤
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
  let state :=
    fun A source =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedCanonicalAssembledCurrentValueFixedBackgroundL2
        H N hN beta hbeta C A distinguishedSource source
        F hF bound hbound
  let localPart :=
    fun A source =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2
        H N hN beta hbeta C A distinguishedSource source (F source)
  let response :=
    fun A source target =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseCurrentValueFixedBackgroundL2
        H N hN beta hbeta C A distinguishedSource source target
        (F target) (hF target) (bound target) (hbound target) C
  let localProfile :=
    fun A source =>
      |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalMean
        H N hN beta hbeta C A distinguishedSource source (F source)|
  have hDecomp :
      ∀ᵐ A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C,
        ∀ source,
          state A source =
            localPart A source + ∑ target, response A source target := by
    filter_upwards with A
    intro source
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedCanonicalAssembledCurrentValueFixedBackgroundL2_eq_localPart_add_sum_targetResponse
        H N hN beta hbeta C A distinguishedSource source
        F hF bound hbound
  have hLocal :
      ∀ᵐ A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C,
        ∀ source,
          ‖localPart A source‖ ≤ localProfile A source := by
    filter_upwards with A
    intro source
    have hEq :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateCurrentValueDiagonalLocalPartFixedBackgroundL2_norm_eq_abs
        H N hN beta hbeta C A distinguishedSource source (F source)
    simpa [localPart, localProfile] using hEq.le
  have hResponse :
      ∀ᵐ A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta C,
        ∀ source target,
          ‖response A source target‖ ≤
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
              H N hN beta hbeta A).influence target source *
              ‖state A target‖ := by
    filter_upwards [hRMSMajorant] with A hRMS
    intro source target
    have hBase :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseCurrentValueFixedBackgroundL2_norm_le_physicalEnvelope_mul_secondMeanRMSAmplitudeCurrentValueFixedBackgroundL2_norm
        N hN s hs beta hbeta hcut H C A distinguishedSource source target
        (F target) (hF target) (bound target) (hbound target) C
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
      N hN s hs beta hbeta hcut H
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C)
      (fun A source =>
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointCurrentValueFixedBackgroundSourcePairL2
          H N hN beta hbeta C A distinguishedSource source)
      state localPart response localProfile
      hDecomp hLocal hResponse
  simpa [state, localPart, response, localProfile] using hSchur

end

end MGAP4D.MathlibAnalytic
