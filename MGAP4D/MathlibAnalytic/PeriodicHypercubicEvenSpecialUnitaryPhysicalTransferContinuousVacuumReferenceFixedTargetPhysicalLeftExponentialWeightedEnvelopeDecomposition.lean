import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResolventMass
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionFixedTargetPhysicalLeftInfluenceEnvelope
import Mathlib.Tactic

/-!
# Fixed-target physical envelope under the growing exponential weight

For a fixed distinguished right target, the exact physical left-left envelope
has one extra bookkeeping point beyond the source-aligned physical envelope:
the distinguished target itself.  This file isolates that point explicitly.

Pointwise, the fixed-target envelope is bounded by

* the genuine 18-neighbor local Harnack kernel,
* one distinguished-target Harnack pin,
* the unchanged source-aligned actual remote residual.

After multiplying by the target-centered exponential base-L1 weight and
summing over physical targets, the fixed-target weighted column is therefore
bounded by the volume-independent local coefficient, one pinned target term,
and the actual weighted remote residual column.

No coarse tagged eligible-row coefficient and no assumed remote coefficient
are introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance fixedTargetExponentialWeightedEnvelopeDecompositionSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The only difference between the fixed-target physical envelope and the
source-aligned local-plus-remote envelope can be overbounded by one Harnack
pin at the distinguished target. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel_le_local_add_targetPin_add_sourceAlignedRemote
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedTarget target source :
      PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A distinguishedTarget).influence target source ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence target source +
        (if target = distinguishedTarget then
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta
        else 0) +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
          H N hN beta hbeta A source target := by
  classical
  let eta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
      beta
  have hEta : 0 ≤ eta := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_nonneg
        beta hbeta
  have hLocal :
      0 ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence target source :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
      H beta hbeta).influence_nonneg target source
  have hRemote :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
          H N hN beta hbeta A source target :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_nonneg
      H N hN beta hbeta A source target
  by_cases hEq : target = source
  · subst target
    have hFixed :
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A distinguishedTarget).influence source source = 0 :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A distinguishedTarget).influence_diagonal_zero source
    rw [hFixed]
    exact add_nonneg (add_nonneg hLocal (by split <;> positivity)) hRemote
  · by_cases hDist : target = distinguishedTarget
    · have hExceptional :
          target ∈
            periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
              H source distinguishedTarget := by
        simp [
          periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers,
          hDist]
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel_eq_harnack_of_exceptional
          H N hN beta hbeta A distinguishedTarget target source hEq hExceptional]
      rw [if_pos hDist]
      change eta ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
            H beta hbeta).influence target source +
          eta +
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
            H N hN beta hbeta A source target
      exact
        (le_add_of_nonneg_left hLocal).trans
          (le_add_of_nonneg_right hRemote)
    · by_cases hActive :
        target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source
      · have hExceptional :
            target ∈
              periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
                H source distinguishedTarget := by
          simp [
            periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers,
            hActive]
        have hRemoteZero :
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
              H N hN beta hbeta A source target = 0 :=
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_eq_zero_of_active
            H N hN beta hbeta A source target hActive
        rw [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel_eq_harnack_of_exceptional
            H N hN beta hbeta A distinguishedTarget target source hEq hExceptional,
          hRemoteZero]
        simp [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel,
          hActive, hDist, eta]
      · have hNotExceptional :
            target ∉
              periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
                H source distinguishedTarget := by
          simp [
            periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers,
            hEq, hDist, hActive]
        have hSourceRemote :
            target ∈
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
                H source source :=
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReference_mem_C5RemoteTargetFibers_source_iff
            H source target).mpr ⟨hEq, hActive⟩
        have hDistRemote :
            target ∈
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
                H source distinguishedTarget := by
          simpa [
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers] using
            hNotExceptional
        have hFixedRemote :
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
                H N hN beta hbeta A distinguishedTarget).influence target source =
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual
                H N hN beta hbeta A source distinguishedTarget target :=
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel_eq_remoteResidual_of_remote
            H N hN beta hbeta A distinguishedTarget target source hDistRemote
        have hResidualEq :
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual
                H N hN beta hbeta A source distinguishedTarget target =
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
                H N hN beta hbeta A source target := by
          unfold
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual
          rw [if_pos hDistRemote, if_pos hSourceRemote]
        rw [hFixedRemote, hResidualEq]
        simp [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel,
          hActive, hDist]

/-- The target-centered weighted fixed-target envelope column is controlled by
the genuine local weighted coefficient, one distinguished-target Harnack pin,
and the actual source-aligned weighted remote residual column. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel_exponentialWeightedColumn_le_local_add_targetPin_add_remote
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (distinguishedTarget source :
      PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A distinguishedTarget).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget target) ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget source +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget distinguishedTarget +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
        H N hN beta hbeta A s distinguishedTarget source := by
  classical
  let eta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
      beta
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s distinguishedTarget
  have hsNonneg : 0 ≤ s := le_trans (by norm_num) hs
  have hWeightNonneg : ∀ target, 0 ≤ W target := by
    intro target
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
        H s hsNonneg distinguishedTarget target
  have hPointwise :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A distinguishedTarget).influence target source * W target ≤
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
              H beta hbeta).influence target source +
            (if target = distinguishedTarget then eta else 0) +
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
              H N hN beta hbeta A source target) * W target := by
    intro target
    exact mul_le_mul_of_nonneg_right
      (by
        simpa [eta] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel_le_local_add_targetPin_add_sourceAlignedRemote
            H N hN beta hbeta A distinguishedTarget target source)
      (hWeightNonneg target)
  have hSum :
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A distinguishedTarget).influence target source * W target) ≤
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
              H beta hbeta).influence target source * W target) +
        eta * W distinguishedTarget +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
          H N hN beta hbeta A s distinguishedTarget source := by
    calc
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A distinguishedTarget).influence target source * W target) ≤
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
              H beta hbeta).influence target source +
            (if target = distinguishedTarget then eta else 0) +
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
              H N hN beta hbeta A source target) * W target := by
          exact Finset.sum_le_sum fun target _ => hPointwise target
      _ =
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
              H beta hbeta).influence target source * W target) +
        eta * W distinguishedTarget +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
          H N hN beta hbeta A s distinguishedTarget source := by
          simp_rw [add_mul]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          have hPin :
              (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
                (if target = distinguishedTarget then eta else 0) * W target) =
                eta * W distinguishedTarget := by
            simp
          rw [hPin]
          unfold
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
          rfl
  have hLocal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_exponentialWeightedColumnSum_le
      H beta hbeta s hs distinguishedTarget source
  calc
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A distinguishedTarget).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget target) ≤
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
            H beta hbeta).influence target source *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s distinguishedTarget target) +
      eta *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget distinguishedTarget +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
        H N hN beta hbeta A s distinguishedTarget source := by
      simpa [W] using hSum
    _ ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget source +
      eta *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget distinguishedTarget +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
        H N hN beta hbeta A s distinguishedTarget source := by
      exact add_le_add_right
        (add_le_add_right hLocal
          (eta *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s distinguishedTarget distinguishedTarget))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
          H N hN beta hbeta A s distinguishedTarget source)
    _ =
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget source +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s distinguishedTarget distinguishedTarget +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
        H N hN beta hbeta A s distinguishedTarget source := by
      rfl

end

end MathlibAnalytic
end MGAP4D
