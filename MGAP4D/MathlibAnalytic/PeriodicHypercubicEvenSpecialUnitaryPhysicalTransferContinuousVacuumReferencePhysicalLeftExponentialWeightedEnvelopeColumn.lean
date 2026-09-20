import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftLocalHarnackExponentialWeightedResolvent
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftLocalHarnackRemotePerturbation
import Mathlib.Tactic

/-!
# Exponentially weighted physical-left envelope column

The full physical left influence envelope is the exact sum of the intrinsic
active-neighbor local Harnack carrier and the source-aligned actual remote
physical residual.

For the growing base-L1 weight
  W_center(x) = s ^ baseL1Distance(center, x),
the local part is already bounded by
  rho_local,s * W_center(source),
where rho_local,s = 18 * eta(beta) * s^2.

This file isolates the remaining spatial problem exactly as the exponentially
weighted column of the actual remote residual. No estimate on that remote
column is assumed or manufactured here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance physicalLeftExponentialWeightedEnvelopeColumnSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (s : ℝ)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
        H N hN beta hbeta A source target *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s center target

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (s : ℝ)
    (hs : 0 ≤ s)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
        H N hN beta hbeta A s center source := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
  exact Finset.sum_nonneg fun target _ =>
    mul_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_nonneg
        H N hN beta hbeta A source target)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
        H s hs center target)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_exponentialWeightedColumn_eq_local_add_remote
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (s : ℝ)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target) =
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence target source *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center target) +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
        H N hN beta hbeta A s center source := by
  classical
  calc
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target) =
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
            H beta hbeta).influence target source +
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationKernel
            H N hN beta hbeta A target source) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center target := by
      apply Finset.sum_congr rfl
      intro target _hTarget
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_eq_localHarnack_add_remotePerturbationKernel]
    _ =
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence target source *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center target) +
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationKernel
            H N hN beta hbeta A target source *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center target := by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
    _ =
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence target source *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center target) +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
        H N hN beta hbeta A s center source := by
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationKernel
      rfl

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_exponentialWeightedColumnSum_le
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
        H beta hbeta).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target) ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source := by
  calc
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
        H beta hbeta).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target) =
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence source target *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center target := by
      apply Finset.sum_congr rfl
      intro target _hTarget
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_influence_comm]
    _ ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_exponentialWeightedRowSum_le
        H beta hbeta s hs center source

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_exponentialWeightedColumnSum_le_local_add_remote
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target) ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
        H N hN beta hbeta A s center source := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_exponentialWeightedColumn_eq_local_add_remote]
  exact
    add_le_add_right
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel_exponentialWeightedColumnSum_le
        H beta hbeta s hs center source)
      _

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_exponentialWeightedColumnSum_le_totalCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (s kappa : ℝ)
    (hs : 1 ≤ s)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRemote :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
          H N hN beta hbeta A s center source ≤
        kappa *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center source) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target) ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2 +
        kappa) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source := by
  have hBase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_exponentialWeightedColumnSum_le_local_add_remote
      H N hN beta hbeta A s hs center source
  calc
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target) ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
        H N hN beta hbeta A s center source := hBase
    _ ≤
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source +
      kappa *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source :=
      add_le_add_left hRemote _
    _ =
      (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2 +
        kappa) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source := by
      ring

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_exponentialWeightedColumnSum_lt_weight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (s kappa : ℝ)
    (hs : 1 ≤ s)
    (hTotal :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
        s ^ 2 +
        kappa < 1)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRemote :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftExponentialWeightedRemoteResidualColumn
          H N hN beta hbeta A s center source ≤
        kappa *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center source) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A).influence target source *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target) <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s center source := by
  have hsPos : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hWeightPos :
      0 <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_pos
      H s hsPos center source
  have hBound :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_exponentialWeightedColumnSum_le_totalCoefficient
      H N hN beta hbeta A s kappa hs center source hRemote
  exact hBound.trans_lt (by
    simpa using
      (mul_lt_mul_of_pos_right hTotal hWeightPos))

end

end MathlibAnalytic
end MGAP4D
