import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectTerminalProfileRenewal
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageTransposeSchurReceiver
import Mathlib.Tactic

/-!
# Terminal-profile Schur feedback receiver

The terminal profile from PR #4896 is the exact link-indexed energy carrier for
the second same-color sweep.  The existing transpose Schur theorem already
turns any one-sided profile relation of the form

  terminal(source)
    <= local(source) + sum_target K(target,source) * terminal(target)

into a volume-uniform energy estimate.

This file specializes that receiver with

* terminal = the PR #4896 terminal second-sweep profile;
* local = the original first-sweep stage profile.

The resulting coefficient-preserving estimate is

  (1 - q_phys)^2 * terminalSweepPathLoss
    <= originalSweepPathLoss.

It is then combined with the six-color defect renewal to expose the exact
two-input receiver needed downstream.  No semantic source-update estimate is
asserted here; the one-sided relation remains an explicit premise.

No division, response symmetry, positive-beta commutativity, finite-cardinality
factor, or factor two is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance terminalProfileSchurFeedbackSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- A transpose one-sided inequality for the terminal profile yields a
coefficient-preserving feedback bound from terminal path loss to the original
one-pass path loss. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepPathLoss_feedback_of_transposeOneSided
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hOneSided :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile
              H N hN beta hbeta f source ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
              H N hN beta hbeta f source +
            ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
                H N hN beta hbeta A).influence target source *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile
                  H N hN beta hbeta f target) :
    (1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
          s beta) ^ 2 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepPathLoss
        H N hN beta hbeta f ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
        H N hN beta hbeta f := by
  let terminalProfile : PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile
      H N hN beta hbeta f
  let localProfile : PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
      H N hN beta hbeta f
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
      s beta
  have hTerminalNonneg : ∀ e, 0 ≤ terminalProfile e := by
    intro e
    simpa [terminalProfile] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile_nonneg
        H N hN beta hbeta f e
  have hLocalNonneg : ∀ e, 0 ≤ localProfile e := by
    intro e
    simpa [localProfile] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_nonneg
        H N hN beta hbeta f e
  have hSchur :
      (1 - q) ^ 2 *
          ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, terminalProfile e ^ 2 ≤
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, localProfile e ^ 2 := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_transpose_oneSided_global_energy_coercive_uniform
        N hN s hs beta hbeta hcut H A
        terminalProfile localProfile hTerminalNonneg hLocalNonneg
        (by
          intro source
          simpa [terminalProfile, localProfile] using hOneSided source)
  have hScaled :=
    mul_le_mul_of_nonneg_left hSchur (show 0 ≤ (1 / 6 : ℝ) by norm_num)
  have hTerminalEq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile_normalized_sq_sum_eq_terminalSweepPathLoss
      H N hN beta hbeta f
  have hLocalEq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_normalized_sq_sum_eq_sweepPathLoss
      H N hN beta hbeta f
  calc
    (1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
          s beta) ^ 2 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepPathLoss
        H N hN beta hbeta f =
      (1 / 6 : ℝ) *
        ((1 - q) ^ 2 *
          ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, terminalProfile e ^ 2) := by
            rw [← hTerminalEq]
            simp only [terminalProfile, q]
            ring
    _ ≤
      (1 / 6 : ℝ) *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, localProfile e ^ 2 :=
      hScaled
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
        H N hN beta hbeta f := by
          simpa [localProfile] using hLocalEq

/-- Averaged renewal receiver: a contraction of the next mean defect makes the
terminal path loss control `(1-rho)` times the current mean defect. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepPathLoss_ge_one_sub_rho_mul_defectMean
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (rho : ℝ)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hnext :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkNextSweepBlockDefectMeanNormSq
          H N hN beta hbeta f ≤
        rho *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
            H N hN beta hbeta f) :
    (1 - rho) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
          H N hN beta hbeta f ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepPathLoss
        H N hN beta hbeta f := by
  have hRenew :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq_eq_terminalSweepPathLoss_add_nextDefectMeanNormSq
      H N hN beta hbeta f
  linarith

/-- Combined coefficient-preserving receiver.

If the next mean defect contracts by `rho` and the terminal profile satisfies
the transpose one-sided response inequality, then the original one-pass path
loss controls the current mean defect with the two strict factors still kept
multiplicatively on the left. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLink_schurFactor_mul_one_sub_rho_mul_defectMean_le_sweepPathLoss
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (rho : ℝ)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hnext :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkNextSweepBlockDefectMeanNormSq
          H N hN beta hbeta f ≤
        rho *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
            H N hN beta hbeta f)
    (hOneSided :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile
              H N hN beta hbeta f source ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
              H N hN beta hbeta f source +
            ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
                H N hN beta hbeta A).influence target source *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile
                  H N hN beta hbeta f target) :
    (1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
          s beta) ^ 2 *
      ((1 - rho) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
          H N hN beta hbeta f) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
        H N hN beta hbeta f := by
  have hRenew :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepPathLoss_ge_one_sub_rho_mul_defectMean
      H N hN beta hbeta rho f hnext
  have hFeedback :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepPathLoss_feedback_of_transposeOneSided
      N hN s hs beta hbeta hcut H A f hOneSided
  have hFactorNonneg :
      0 ≤
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
            s beta) ^ 2 :=
    sq_nonneg _
  exact
    (mul_le_mul_of_nonneg_left hRenew hFactorNonneg).trans hFeedback

end

end MGAP4D.MathlibAnalytic
