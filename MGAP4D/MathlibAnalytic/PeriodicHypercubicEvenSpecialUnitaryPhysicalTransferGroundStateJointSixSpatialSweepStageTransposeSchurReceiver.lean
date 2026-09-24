import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageSchurReceiver
import MGAP4D.MathlibAnalytic.FiniteNonnegativeInfluenceKernelBidirectionalSchurL2
import Mathlib.Tactic

/-!
# Transpose Schur receiver for the physical sweep-stage profile

The source-uniform centered RMS theorem of PR #4711 naturally propagates a
target amplitude into a source coordinate with coefficient K(target,source).
Thus the relevant stationary one-sided recurrence is transpose-oriented:

  u(source) <= ell(source) + sum_target K(target,source) * u(target).

The physical envelope already has both row and column sums bounded by the same
volume-independent coefficient q_phys.  Hence the transpose action has the
same L2 Schur norm.  This file packages that fact and supplies the transpose
ground-state sweep-stage receiver.

No new influence matrix is introduced.  Only the two indices of the already
canonical physical envelope are exchanged when applying the finite Schur
lemma.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance transposeSchurReceiverSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance transposeSchurReceiverSpatialLinkNonempty
    (H : ℕ) :
    Nonempty (PeriodicHypercubicEvenSpatialSliceLink H) :=
  ⟨(⟨(0 : PeriodicHypercubicEvenVertex H), by
      simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
    ⟨(1 : PeriodicHypercubicAxis), by norm_num⟩)⟩

local instance transposeSchurReceiverSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- Uniform L2 Schur estimate for the transpose action of the actual physical
influence envelope.  The same q_phys works because the original envelope has
both row and column sums bounded by q_phys. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_transpose_action_sq_sum_le_uniformBidirectionalSchurCoefficient_sq
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (vector : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) :
    (∑ source,
      (∑ target,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A).influence target source *
          vector target) ^ 2) ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
        s beta) ^ 2 *
        ∑ target, vector target ^ 2 := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
      H N hN beta hbeta A
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
      s beta
  have hq0 : 0 ≤ q := by
    simpa [q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient_nonneg
        s hs beta hbeta hcut
  have hRow : ∀ target, finiteInfluenceKernelRowSum K target ≤ q := by
    intro target
    exact
      (finiteInfluenceKernelRowSum_le_maximum K target).trans
        (by
          simpa [K, q] using
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_maximumRow_le_uniformBidirectionalSchurCoefficient
              N hN s hs beta hbeta hcut H A)
  have hColumn : ∀ source, finiteInfluenceKernelColumnSum K source ≤ q := by
    intro source
    exact
      (finiteInfluenceKernelColumnSum_le_maximum K source).trans
        (by
          simpa [K, q] using
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_maximumColumn_le_uniformBidirectionalSchurCoefficient
              N hN s hs beta hbeta hcut H A)
  have hSchur :=
    FiniteNonnegativeSchur.action_sq_sum_le_row_mul_column
      (fun source target => K.influence target source)
      (fun source target => K.influence_nonneg target source)
      q q hq0
      (by
        intro source
        simpa [finiteInfluenceKernelColumnSum] using hColumn source)
      (by
        intro target
        simpa [finiteInfluenceKernelRowSum] using hRow target)
      vector
  simpa [K, q, pow_two] using hSchur

/-- Uniform one-sided coercivity for a transpose-Dobrushin subinvariant
profile.  This is the orientation generated by the canonical heat-bath update
algebra and by PR #4711. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_transpose_oneSided_global_energy_coercive_uniform
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (profile localProfile : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hProfileNonneg : ∀ e, 0 ≤ profile e)
    (hLocalNonneg : ∀ e, 0 ≤ localProfile e)
    (hOneSided : ∀ source,
      profile source ≤
        localProfile source +
          ∑ target,
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
              H N hN beta hbeta A).influence target source *
              profile target) :
    (1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
          s beta) ^ 2 *
        ∑ e, profile e ^ 2 ≤
      ∑ e, localProfile e ^ 2 := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
      H N hN beta hbeta A
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
      s beta
  have hq0 : 0 ≤ q := by
    simpa [q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient_nonneg
        s hs beta hbeta hcut
  have hq1 : q < 1 := by
    simpa [q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient_lt_one
        s beta hbeta hcut
  have hSchur : ∀ vector : PeriodicHypercubicEvenSpatialSliceLink H → ℝ,
      (∑ source,
        (∑ target, K.influence target source * vector target) ^ 2) ≤
        q ^ 2 * ∑ target, vector target ^ 2 := by
    intro vector
    simpa [K, q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_transpose_action_sq_sum_le_uniformBidirectionalSchurCoefficient_sq
        N hN s hs beta hbeta hcut H A vector
  exact
    FiniteSchurOneSidedProfile.global_energy_coercive
      (fun source target => K.influence target source)
      q hq0 hq1
      (fun source target => K.influence_nonneg target source)
      hSchur
      profile localProfile hProfileNonneg hLocalNonneg
      (by
        intro source
        simpa [K] using hOneSided source)

/-- Feed the genuine six-spatial sweep-stage local profile into the transpose
receiver.  The normalization and residual-energy right side are exactly the
same as in the row-oriented receiver. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfile_transposeOneSided_global_energy_coercive_uniform
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
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
    (hOneSided : ∀ source,
      profile source ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
            H N hN beta hbeta f source +
          ∑ target,
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
              H N hN beta hbeta A).influence target source *
              profile target) :
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
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_transpose_oneSided_global_energy_coercive_uniform
        N hN s hs beta hbeta hcut H A
        profile localProfile hProfileNonneg hLocalNonneg
        (by
          intro source
          simpa [localProfile] using hOneSided source)
  have hSix : (0 : ℝ) ≤ 1 / 6 := by norm_num
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

/-- Transpose-oriented relative Poincare receiver.  As before, the global
profile majorant remains a separate premise. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfile_relativePoincare_of_transposeOneSided_and_globalMajorant
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
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
    (hOneSided : ∀ source,
      profile source ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
            H N hN beta hbeta f source +
          ∑ target,
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
              H N hN beta hbeta A).influence target source *
              profile target)
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
  have hSix : (0 : ℝ) ≤ 1 / 6 := by norm_num
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
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfile_transposeOneSided_global_energy_coercive_uniform
        N hN s hs beta hbeta hcut H A f profile
        hProfileNonneg hOneSided)

end

end MGAP4D.MathlibAnalytic
