import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointTerminalProfileSchurFeedback
import Mathlib.Tactic

/-!
# Beta-small terminal-profile Schur feedback

PR #4898 packages the coefficient-one terminal-profile receiver

  terminal <= original + Kᵀ terminal

into

  (1-q_phys)^2 * Lterm <= L.

For the defect-margin route this file keeps the sharper forcing structure
needed near beta = 0.  If the semantic recurrence has the form

  terminal <= Kᵀ original + Kᵀ terminal,

then the same transpose Schur estimate is applied twice:

* once to absorb the terminal feedback;
* once to bound the forced original profile.

This yields

  (1-q_phys)^2 * Lterm <= q_phys^2 * L,

with no coefficient-one weakening.  The explicit q_phys also vanishes at the
decoupled endpoint.

No response symmetry, positive-beta commutativity, finite-cardinality factor,
factor two, or division by (1-q_phys) is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance terminalProfileBetaSmallSchurFeedbackSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The canonical bidirectional Schur coefficient vanishes at beta = 0. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient_zero
    (s : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
        s 0 = 0 := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence]

/-- Sharpened terminal feedback receiver.

If both the external forcing and the terminal feedback arrive through the same
transpose physical influence kernel, then the original one-pass path loss
carries an additional factor q_phys^2.  This is the coefficient-preserving
form needed by the small-beta defect-margin argument. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepPathLoss_betaSmallFeedback_of_transposeForcing
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
          (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
              H N hN beta hbeta A).influence target source *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
                H N hN beta hbeta f target) +
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
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
          s beta) ^ 2 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
          H N hN beta hbeta f := by
  let terminalProfile : PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile
      H N hN beta hbeta f
  let localProfile : PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
      H N hN beta hbeta f
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
      H N hN beta hbeta A
  let forcedProfile : PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    fun source =>
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        K.influence target source * localProfile target
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
  have hForcedNonneg : ∀ e, 0 ≤ forcedProfile e := by
    intro source
    dsimp [forcedProfile]
    exact Finset.sum_nonneg fun target _ =>
      mul_nonneg (K.influence_nonneg target source) (hLocalNonneg target)
  have hTerminalCoercive :
      (1 - q) ^ 2 *
          ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, terminalProfile e ^ 2 ≤
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, forcedProfile e ^ 2 := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_transpose_oneSided_global_energy_coercive_uniform
        N hN s hs beta hbeta hcut H A
        terminalProfile forcedProfile hTerminalNonneg hForcedNonneg
        (by
          intro source
          simpa [terminalProfile, localProfile, K, forcedProfile] using
            hOneSided source)
  have hForcedEnergy :
      (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        forcedProfile source ^ 2) ≤
        q ^ 2 *
          ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            localProfile target ^ 2 := by
    simpa [forcedProfile, localProfile, K, q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_transpose_action_sq_sum_le_uniformBidirectionalSchurCoefficient_sq
        N hN s hs beta hbeta hcut H A localProfile
  have hEnergy :
      (1 - q) ^ 2 *
          ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, terminalProfile e ^ 2 ≤
        q ^ 2 *
          ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, localProfile e ^ 2 :=
    hTerminalCoercive.trans hForcedEnergy
  have hScaled :=
    mul_le_mul_of_nonneg_left hEnergy (show 0 ≤ (1 / 6 : ℝ) by norm_num)
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
        (q ^ 2 *
          ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, localProfile e ^ 2) :=
      hScaled
    _ =
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
          s beta) ^ 2 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
          H N hN beta hbeta f := by
            rw [← hLocalEq]
            simp only [localProfile, q]
            ring

end

end MGAP4D.MathlibAnalytic
