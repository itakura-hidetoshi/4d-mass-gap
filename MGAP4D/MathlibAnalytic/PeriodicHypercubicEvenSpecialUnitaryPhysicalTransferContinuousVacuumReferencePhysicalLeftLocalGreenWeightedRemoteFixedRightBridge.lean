import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteConvolution
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTargetWorstCaseCrossRatioInfluenceMajorant
import Mathlib.Tactic

/-!
# Bridge weighted physical-left remote convolution to fixed-right finite-step response

The source-aligned physical residual used by the local-Harnack perturbation
machinery is an actual conditional-law influence majorant.  On its remote set
it is exactly the targetwise worst-case transformed fixed-right cross-ratio
majorant.  The latter already has a finite-step response bound which does not
assume covariance decay.

This file records that pointwise bridge and lifts it through the base-L1 local
Green weight.  Thus the opaque remote residual in the current singleton
comparison is replaced by an explicit targetwise fixed-right finite-step
response profile, without using terminal covariance decay and without
collapsing the intermediate spatial coordinate.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance physicalLeftLocalGreenWeightedRemoteFixedRightBridgeSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Every source-aligned physical remote residual is bounded by the existing
fixed-right finite-step target response bound.

On the actual remote set this is exactly the worst-case cross-ratio theorem.
Off that set the physical residual is zero, while the finite-step tagged bound
is nonnegative.  No covariance-decay or terminal-response-vanishing premise is
introduced. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_le_exp_sixteen_mul_nStepTargetBound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
        H N hN beta hbeta A source target ≤
      Real.exp (16 * beta) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
              H beta target)
            n (Sum.inr source) +
          2 *
            ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
                H beta hbeta
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
                  H beta target)
                n (Sum.inl e)) := by
  classical
  by_cases hRemote :
      target ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
          H source source
  · have hNotExceptional :
        target ∉
          periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
            H source source := by
      simpa [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers] using
        hRemote
    rcases
      periodicHypercubicEvenSpatialSlice_not_mem_C5ExceptionalBackgroundFibers
        H source source target hNotExceptional with
      ⟨hSourceTarget, _hTargetDistinguished, hNoShare⟩
    have hWorst :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant_le_exp_sixteen_mul_nStepTargetBound_of_remote
        H N hN beta hbeta A
        (target := target) (source := source)
        (Ne.symm hSourceTarget) hNoShare n
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual,
      hRemote] using hWorst
  · have hVariationNonneg :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_nonneg
        H beta target
    have hRight :
        0 ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
              H beta target)
            n (Sum.inr source) :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate_nonneg
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
          H beta target)
        hVariationNonneg n (Sum.inr source)
    have hLeft :
        0 ≤
          ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
              H beta hbeta
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
                H beta target)
              n (Sum.inl e) := by
      exact Finset.sum_nonneg fun e _ =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate_nonneg
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
            H beta target)
          hVariationNonneg n (Sum.inl e)
    have hRhs :
        0 ≤
          Real.exp (16 * beta) *
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
                H beta hbeta
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
                  H beta target)
                n (Sum.inr source) +
              2 *
                ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
                  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
                    H beta hbeta
                    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
                      H beta target)
                    n (Sum.inl e)) := by
      exact
        mul_nonneg (Real.exp_pos _).le
          (add_nonneg hRight (mul_nonneg (by norm_num) hLeft))
    have hZero :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
            H N hN beta hbeta A source target = 0 := by
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual
      simp [hRemote]
    rw [hZero]
    exact hRhs

/-- The fixed-right finite-step profile obtained after one local Green
propagation.  It keeps the intermediate spatial link explicit and is
configuration-independent. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteNStepFixedRightTargetBound
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (n : ℕ) : ℝ :=
  ∑ mid : PeriodicHypercubicEvenSpatialSliceLink H,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1GreenWeight
        H beta target mid *
      (Real.exp (16 * beta) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
              H beta mid)
            n (Sum.inr source) +
          2 *
            ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
                H beta hbeta
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
                  H beta mid)
                n (Sum.inl e)))

/-- The actual local-Green weighted remote column is bounded by the explicit
fixed-right finite-step profile. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteColumn_le_nStepFixedRightTargetBound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hThreshold :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta <
        1)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteColumn
        H N hN beta hbeta A target source ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteNStepFixedRightTargetBound
        H beta hbeta target source n := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteColumn
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteNStepFixedRightTargetBound
  apply Finset.sum_le_sum
  intro mid _hmid
  exact
    mul_le_mul_of_nonneg_left
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_le_exp_sixteen_mul_nStepTargetBound
        H N hN beta hbeta A source mid n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1GreenWeight_nonneg
        H beta hbeta hThreshold target mid)

/-- Consequently the local Green response to the actual remote forcing is
controlled by a configuration-independent fixed-right finite-step weighted
kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_remoteForcing_le_nStepFixedRightWeightedBound
    (H N M : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hThreshold :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta <
        1)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hwNonneg : ∀ source, 0 ≤ w source)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (n : ℕ) :
    finiteNonnegativeKernelPartialResolvent
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing
          H N hN beta hbeta A w)
        M target ≤
      ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteNStepFixedRightTargetBound
            H beta hbeta target source n *
          w source := by
  calc
    finiteNonnegativeKernelPartialResolvent
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing
          H N hN beta hbeta A w)
        M target ≤
      ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteColumn
            H N hN beta hbeta A target source *
          w source :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_remoteForcing_le_weightedRemoteConvolution
        H N M hN beta hbeta hThreshold A w hwNonneg target
    _ ≤
      ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteNStepFixedRightTargetBound
            H beta hbeta target source n *
          w source := by
      apply Finset.sum_le_sum
      intro source _hsource
      exact
        mul_le_mul_of_nonneg_right
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteColumn_le_nStepFixedRightTargetBound
            H N hN beta hbeta hThreshold A target source n)
          (hwNonneg source)

/-- Singleton physical-envelope comparison with the remote term replaced by the
configuration-independent fixed-right finite-step weighted response profile.

The direct source term still carries the base-L1 geometric decay from the local
Harnack Green kernel.  The new middle term is now expressed entirely through
the fixed-right finite-step response machinery. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeft_singleton_localGeometric_add_nStepFixedRightWeightedRemoteBound_add_remainder
    (H N D M : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hThreshold :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta <
        1)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistance :
      2 * D ≤
        periodicHypercubicEdgeBaseL1Distance
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source))
    (amplitude : ℝ)
    (hAmplitude : 0 ≤ amplitude)
    (w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hwNonneg : ∀ t, 0 ≤ w t)
    (distanceBound : ℝ)
    (hDistanceBound : 0 ≤ distanceBound)
    (hwBound : ∀ t, w t ≤ distanceBound)
    (hComparison :
      ∀ t,
        w t ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackSingletonForcing
              source amplitude t +
            finiteNonnegativeKernelApply
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
                H N hN beta hbeta A).influence
              w t)
    (n : ℕ) :
    w target ≤
      ((18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta) ^ D /
        (1 -
          18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta)) *
          amplitude +
        (∑ s : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteNStepFixedRightTargetBound
              H beta hbeta target s n *
            w s) +
        (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta) ^ M * distanceBound := by
  have hBase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeft_singleton_localGeometric_add_weightedRemoteConvolution_add_remainder
      H N D M hN beta hbeta hThreshold A source target hDistance
      amplitude hAmplitude w hwNonneg distanceBound hDistanceBound hwBound hComparison
  calc
    w target ≤
      ((18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta) ^ D /
        (1 -
          18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta)) *
          amplitude +
        (∑ s : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteColumn
              H N hN beta hbeta A target s *
            w s) +
        (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta) ^ M * distanceBound :=
      hBase
    _ ≤
      ((18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta) ^ D /
        (1 -
          18 *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
              beta)) *
          amplitude +
        (∑ s : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteNStepFixedRightTargetBound
              H beta hbeta target s n *
            w s) +
        (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta) ^ M * distanceBound := by
      apply add_le_add_right
      apply add_le_add_left
      apply Finset.sum_le_sum
      intro s _hs
      exact
        mul_le_mul_of_nonneg_right
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteColumn_le_nStepFixedRightTargetBound
            H N hN beta hbeta hThreshold A target s n)
          (hwNonneg s)

end

end MathlibAnalytic
end MGAP4D
