import MGAP4D.MathlibAnalytic.FiniteNonnegativeInfluenceKernelBidirectionalSchurL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepGate
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeRemoteRowObstruction
import Mathlib.Tactic

/-!
# Bidirectional Schur gate for the physical high-temperature influence envelope

This unit combines three already-separated layers:

* the canonical high-temperature strict maximum-column theorem;
* the explicit remote-row obstruction / maximum-row receiver;
* the generic finite nonnegative bidirectional Schur L2 theorem.

The result is deliberately conditional only on the remaining row-oriented
remote-residual estimate.  Once that estimate makes the complete physical row
strictly subunit, the actual physical envelope has a strict bidirectional Schur
coefficient in every finite volume and background.

The final theorem exposes exactly the remaining observable-facing obligation:
a one-sided profile inequality for the same physical envelope.  No bounded-test
contraction is identified with an L2 Poincare theorem without this input.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance physicalBidirectionalSchurGateSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalBidirectionalSchurGateSpatialLinkNonempty
    (H : ℕ) :
    Nonempty (PeriodicHypercubicEvenSpatialSliceLink H) :=
  ⟨(⟨(0 : PeriodicHypercubicEvenVertex H), by
      simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
    ⟨(1 : PeriodicHypercubicAxis), by norm_num⟩)⟩

local instance physicalBidirectionalSchurGateSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- On the canonical strict high-temperature interval, a strict uniform
remote-row bound upgrades the already-proved physical maximum-column
contraction to a strict bidirectional Schur coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_bidirectionalSchurCoefficient_lt_one
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
    (rhoRow : ℝ)
    (hRemoteRow :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHasUniformRemoteResidualRowBound
        N hN beta hbeta rhoRow)
    (hRowStrict :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta +
        rhoRow < 1)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    finiteInfluenceKernelBidirectionalSchurCoefficient
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A) < 1 := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
      H N hN beta hbeta A
  have hRow :
      finiteInfluenceKernelMaximumRowSum K < 1 := by
    simpa [K] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_maximumRow_lt_one_of_uniformRemoteRow
        N hN beta hbeta rhoRow hRemoteRow hRowStrict H A
  have hColumn :
      finiteInfluenceKernelMaximumColumnSum K < 1 := by
    simpa [K] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_maximumColumn_lt_one
        N hN s hs beta hbeta hcut H A
  exact
    (finiteInfluenceKernelBidirectionalSchurCoefficient_lt_one_iff K).2
      ⟨hRow, hColumn⟩

/-- The bidirectional physical Schur gap is strictly positive under the same
row and column hypotheses. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_bidirectionalSchurGap_pos
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
    (rhoRow : ℝ)
    (hRemoteRow :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHasUniformRemoteResidualRowBound
        N hN beta hbeta rhoRow)
    (hRowStrict :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta +
        rhoRow < 1)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 <
      (1 -
        finiteInfluenceKernelBidirectionalSchurCoefficient
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A)) ^ 2 := by
  have hStrict :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_bidirectionalSchurCoefficient_lt_one
      N hN s hs beta hbeta hcut rhoRow hRemoteRow hRowStrict H A
  exact pow_pos (sub_pos.mpr hStrict) 2

/-- Conditional positive-beta L2 profile coercivity for the actual physical
influence envelope.  All finite-dimensional Schur work is discharged here.
The only observable-facing premise left explicit is the one-sided profile
inequality itself. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_oneSided_global_energy_coercive
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
    (rhoRow : ℝ)
    (hRemoteRow :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHasUniformRemoteResidualRowBound
        N hN beta hbeta rhoRow)
    (hRowStrict :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta +
        rhoRow < 1)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (profile localProfile : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hProfileNonneg : ∀ e, 0 ≤ profile e)
    (hLocalNonneg : ∀ e, 0 ≤ localProfile e)
    (hOneSided : ∀ target,
      profile target ≤
        localProfile target +
          ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
              H N hN beta hbeta A).influence target source *
              profile source) :
    (1 -
        finiteInfluenceKernelBidirectionalSchurCoefficient
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A)) ^ 2 *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, profile e ^ 2 ≤
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, localProfile e ^ 2 := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
      H N hN beta hbeta A
  have hStrict :
      finiteInfluenceKernelBidirectionalSchurCoefficient K < 1 := by
    simpa [K] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_bidirectionalSchurCoefficient_lt_one
        N hN s hs beta hbeta hcut rhoRow hRemoteRow hRowStrict H A
  exact
    finiteInfluenceKernelBidirectional_oneSided_global_energy_coercive
      K hStrict profile localProfile
      hProfileNonneg hLocalNonneg
      (by simpa [K] using hOneSided)

end

end MGAP4D.MathlibAnalytic
