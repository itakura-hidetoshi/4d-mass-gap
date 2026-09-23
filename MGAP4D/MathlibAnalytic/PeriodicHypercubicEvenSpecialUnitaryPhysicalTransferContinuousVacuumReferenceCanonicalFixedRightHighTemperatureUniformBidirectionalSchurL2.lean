import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteRowOscillationClosure
import Mathlib.Tactic

/-!
# Uniform bidirectional Schur coefficient for the physical high-temperature envelope

The canonical high-temperature construction now supplies the same explicit
oscillation residual scalar on both orientations of the actual physical
influence envelope.

This file packages the already-integrated row and column estimates under one
volume/background-independent scalar

  q_phys(s,beta)
    = 18 * eta(beta) + rho_osc(s,beta).

On the existing strict physical-sweep interval, q_phys is nonnegative and
strictly below one. Every finite-volume/background physical envelope has both
maximum row and maximum column bounded by q_phys. Hence its action on arbitrary
real link profiles obeys the genuine finite-dimensional Schur estimate

  sum_t (sum_s K(t,s) v(s))^2
    <= q_phys^2 * sum_s v(s)^2.

The corresponding one-sided profile coercivity therefore has the uniform
coefficient (1-q_phys)^2.

This theorem unit still does not assert the observable-specific one-sided
profile inequality. It fixes the volume-uniform L2 coefficient that will be
consumed once that analytic comparison is supplied.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance physicalUniformBidirectionalSchurSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalUniformBidirectionalSchurSpatialLinkNonempty
    (H : ℕ) :
    Nonempty (PeriodicHypercubicEvenSpatialSliceLink H) :=
  ⟨(⟨(0 : PeriodicHypercubicEvenVertex H), by
      simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
    ⟨(1 : PeriodicHypercubicAxis), by norm_num⟩)⟩

local instance physicalUniformBidirectionalSchurSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- Canonical scalar which controls both orientations of the actual physical
influence envelope on the strict high-temperature interval. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
    (s beta : ℝ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient
    beta
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
      s beta)

/-- The canonical uniform bidirectional coefficient is nonnegative throughout
the strict physical-sweep interval. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient_nonneg
    (s : ℝ)
    (hs : 1 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
        s beta := by
  have hHalfCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_le_halfBarrierCutoff
        s)
  have hRho :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
          s beta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound_nonneg
      s beta hs hbeta hHalfCut
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient_nonneg
      beta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
        s beta)
      hbeta hRho

/-- The same canonical coefficient is strictly below one on the existing
strict physical-sweep interval. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient_lt_one
    (s beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
        s beta < 1 := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_spec
      s beta hbeta hcut

/-- Every finite-volume/background maximum row is bounded by the canonical
volume-independent bidirectional coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_maximumRow_le_uniformBidirectionalSchurCoefficient
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
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    finiteInfluenceKernelMaximumRowSum
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
        s beta := by
  have hHalfCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_le_halfBarrierCutoff
        s)
  have hRemoteRow :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperature_remoteResidualOscillationUniformRowBound
      N hN s hs beta hbeta hHalfCut
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_maximumRow_le_of_uniformRemoteRow
      N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
        s beta)
      hRemoteRow H A

/-- Every finite-volume/background maximum column is bounded by the same
canonical volume-independent bidirectional coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_maximumColumn_le_uniformBidirectionalSchurCoefficient
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
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    finiteInfluenceKernelMaximumColumnSum
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
        s beta := by
  have hHalfCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_le_halfBarrierCutoff
        s)
  have hRemoteColumn :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperature_remoteResidualOscillationUniformBound
      N hN s hs beta hbeta hHalfCut
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_maximumColumn_le_uniform
      N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
        s beta)
      hRemoteColumn H A

/-- The exact finite-volume/background bidirectional Schur coefficient is
bounded by the same canonical scalar. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_bidirectionalSchurCoefficient_le_uniform
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
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    finiteInfluenceKernelBidirectionalSchurCoefficient
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
        s beta := by
  unfold finiteInfluenceKernelBidirectionalSchurCoefficient
  exact max_le
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_maximumRow_le_uniformBidirectionalSchurCoefficient
      N hN s hs beta hbeta hcut H A)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_maximumColumn_le_uniformBidirectionalSchurCoefficient
      N hN s hs beta hbeta hcut H A)

/-- Uniform L2 Schur estimate for the actual physical influence envelope.
The coefficient depends only on the fixed high-temperature parameters and not
on the finite volume or background. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_action_sq_sum_le_uniformBidirectionalSchurCoefficient_sq
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
    (vector : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) :
    (∑ target,
      (∑ source,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A).influence target source *
          vector source) ^ 2) ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
        s beta) ^ 2 *
        ∑ source, vector source ^ 2 := by
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
      K.influence K.influence_nonneg
      q q hq0
      (by
        intro target
        simpa [finiteInfluenceKernelRowSum] using hRow target)
      (by
        intro source
        simpa [finiteInfluenceKernelColumnSum] using hColumn source)
      vector
  simpa [K, q, pow_two] using hSchur

/-- Uniform one-sided profile coercivity for the actual physical influence
envelope. The only remaining premise is the observable-specific one-sided
profile comparison itself. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_oneSided_global_energy_coercive_uniform
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
    (profile localProfile : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hProfileNonneg : ∀ e, 0 ≤ profile e)
    (hLocalNonneg : ∀ e, 0 ≤ localProfile e)
    (hOneSided : ∀ target,
      profile target ≤
        localProfile target +
          ∑ source,
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
              H N hN beta hbeta A).influence target source *
              profile source) :
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
      (∑ target, (∑ source, K.influence target source * vector source) ^ 2) ≤
        q ^ 2 * ∑ source, vector source ^ 2 := by
    intro vector
    simpa [K, q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_action_sq_sum_le_uniformBidirectionalSchurCoefficient_sq
        N hN s hs beta hbeta hcut H A vector
  exact
    FiniteSchurOneSidedProfile.global_energy_coercive
      K.influence q hq0 hq1 K.influence_nonneg hSchur
      profile localProfile hProfileNonneg hLocalNonneg
      (by simpa [K] using hOneSided)

end

end MGAP4D.MathlibAnalytic
