import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialOneLinkSweepStageProfile
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurL2
import Mathlib.Tactic

/-!
# Ground-state sweep-stage profile fed into the uniform physical Schur receiver

The preceding theorem unit constructs a genuine spatial-link local amplitude
`ell_e(f)` from the successive one-link residuals of the six color sweeps and
proves

  (1 / 6) * sum_e ell_e(f)^2 <= E_6sp(f).

The uniform physical influence theorem supplies, for every nonnegative profile
`u` satisfying the observable-specific one-sided estimate

  u_t <= ell_t(f) + sum_s K_{t,s} u_s,

the Schur coercivity estimate

  (1 - q_phys)^2 * sum_e u_e^2 <= sum_e ell_e(f)^2.

This file composes those already-proved results.  Thus the only analytic
obligations left before a bounded-core six-spatial Poincare inequality are:

1. construct the actual observable-specific nonnegative profile `u_e(f)`;
2. prove its one-sided physical influence estimate;
3. prove the corresponding global profile majorant.

No new probability geometry, influence estimate, or commutativity assumption
is introduced here.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance groundStateSweepStageSchurReceiverSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance groundStateSweepStageSchurReceiverSpatialLinkNonempty
    (H : ℕ) :
    Nonempty (PeriodicHypercubicEvenSpatialSliceLink H) :=
  ⟨(⟨(0 : PeriodicHypercubicEvenVertex H), by
      simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
    ⟨(1 : PeriodicHypercubicAxis), by norm_num⟩)⟩

local instance groundStateSweepStageSchurReceiverSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- Feed the concrete ground-state sweep-stage local profile into the already
proved volume-uniform one-sided Schur receiver.  The resulting coefficient is
normalized by the six spatial colors, and the right side is the genuine
six-spatial residual energy. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfile_oneSided_global_energy_coercive_uniform
    (N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (profile : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hProfileNonneg : ∀ e, 0 ≤ profile e)
    (hOneSided : ∀ target,
      profile target ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
            H N hN beta hbeta f target +
          ∑ source,
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
              H N hN beta hbeta A).influence target source *
              profile source) :
    (1 / 6 : ℝ) *
        ((1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
            s beta) ^ 2 *
          ∑ e, profile e ^ 2) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
        H N hN beta hbeta f := by
  let localProfile : PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
      H N hN beta hbeta f
  have hLocalNonneg : ∀ e, 0 ≤ localProfile e := by
    intro e
    simpa [localProfile] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_nonneg
        H N hN beta hbeta f e
  have hSchur :
      (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
            s beta) ^ 2 *
          ∑ e, profile e ^ 2 ≤
        ∑ e, localProfile e ^ 2 := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_oneSided_global_energy_coercive_uniform
        N hN s hs beta hbeta hcut H A
        profile localProfile hProfileNonneg hLocalNonneg
        (by
          intro target
          simpa [localProfile] using hOneSided target)
  have hSix : (0 : ℝ) ≤ 1 / 6 := by
    norm_num
  have hScaled :
      (1 / 6 : ℝ) *
          ((1 -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
              s beta) ^ 2 *
            ∑ e, profile e ^ 2) ≤
        (1 / 6 : ℝ) * ∑ e, localProfile e ^ 2 :=
    mul_le_mul_of_nonneg_left hSchur hSix
  exact
    hScaled.trans
      (by
        simpa [localProfile] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_normalized_sq_sum_le_residualEnergy
            H N hN beta hbeta f)

/-- If the future observable-specific profile also majorizes the desired
centered global L2 energy, the preceding receiver immediately yields the
bounded-observable relative Poincare estimate with coefficient
`(1/6) * (1-q_phys)^2`.  The global majorant remains an explicit premise. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfile_relativePoincare_of_oneSided_and_globalMajorant
    (N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (center :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (profile : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hProfileNonneg : ∀ e, 0 ≤ profile e)
    (hOneSided : ∀ target,
      profile target ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
            H N hN beta hbeta f target +
          ∑ source,
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
              H N hN beta hbeta A).influence target source *
              profile source)
    (hGlobal :
      ‖f - center f‖ ^ 2 ≤ ∑ e, profile e ^ 2) :
    (1 / 6 : ℝ) *
        ((1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
            s beta) ^ 2 *
          ‖f - center f‖ ^ 2) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
        H N hN beta hbeta f := by
  have hFactor :
      0 ≤
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
            s beta) ^ 2 :=
    sq_nonneg _
  have hProfileEnergy :
      (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
            s beta) ^ 2 *
          ‖f - center f‖ ^ 2 ≤
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
            s beta) ^ 2 *
          ∑ e, profile e ^ 2 :=
    mul_le_mul_of_nonneg_left hGlobal hFactor
  have hSix : (0 : ℝ) ≤ 1 / 6 := by
    norm_num
  have hScaled :
      (1 / 6 : ℝ) *
          ((1 -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
              s beta) ^ 2 *
            ‖f - center f‖ ^ 2) ≤
        (1 / 6 : ℝ) *
          ((1 -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
              s beta) ^ 2 *
            ∑ e, profile e ^ 2) :=
    mul_le_mul_of_nonneg_left hProfileEnergy hSix
  exact
    hScaled.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfile_oneSided_global_energy_coercive_uniform
        N hN s hs beta hbeta hcut H A f profile
        hProfileNonneg hOneSided)

end

end MGAP4D.MathlibAnalytic
