import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteFixedRightBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioAsymptoticResolvent
import Mathlib.Tactic

/-!
# Close the physical-left local-Green remote bridge at asymptotic fixed-right depth

The finite-step bridge keeps the intermediate spatial link explicit, but still
carries a scan-depth parameter.  The fixed-right asymptotic resolvent removes
that parameter under the current strict eligible-row criterion.

This file transports that asymptotic closure back to the actual source-aligned
remote physical residual and then through the local base-L1 Green convolution.
The C5 remote support is retained explicitly instead of replacing it by a
global constant profile.  The resulting statement is still fixed-volume:
the eligible-row criterion contains the current coarse all-to-all left-left
coefficient.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance physicalLeftLocalGreenWeightedRemoteAsymptoticFixedRightBridgeSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Configuration-independent asymptotic fixed-right envelope for one
source-aligned remote target.  Outside the actual C5 remote set it is exactly
zero, so the support information of the physical residual is preserved. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemoteAsymptoticFixedRightBound
    (H : ℕ)
    (beta : ℝ)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  if target ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
        H source source then
    Real.exp (16 * beta) *
      ((2 *
        (((Real.exp (8 * beta)) ^ 2 - 1) /
          ((Real.exp (8 * beta)) ^ 2 + 1))) *
        (Real.exp (16 * beta) *
          (1 -
            (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
                beta))⁻¹))
  else
    0

/-- The actual source-aligned remote residual is bounded by the asymptotic
fixed-right envelope.  This removes the finite random-scan depth without
discarding the exact C5 remote support. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_le_asymptoticFixedRightBound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hCard : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (hEligibleRowLtOne :
      (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta) < 1)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
        H N hN beta hbeta A source target ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemoteAsymptoticFixedRightBound
        H beta source target := by
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
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant_le_explicitEligibleRow_asymptotic_resolvent_of_remote
        H N hN beta hbeta hCard hEligibleRowLtOne A
        (target := target) (source := source)
        (Ne.symm hSourceTarget) hNoShare
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemoteAsymptoticFixedRightBound,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual,
      hRemote] using hWorst
  · simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemoteAsymptoticFixedRightBound,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual,
      hRemote]

/-- One local Green propagation of the asymptotic fixed-right remote envelope,
with the intermediate spatial link kept explicit. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteAsymptoticFixedRightBound
    (H : ℕ)
    (beta : ℝ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ mid : PeriodicHypercubicEvenSpatialSliceLink H,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1GreenWeight
        H beta target mid *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemoteAsymptoticFixedRightBound
        H beta source mid

/-- The actual local-Green weighted remote column is bounded by the
scan-depth-free asymptotic fixed-right column. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteColumn_le_asymptoticFixedRightBound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hThreshold :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta <
        1)
    (hCard : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (hEligibleRowLtOne :
      (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta) < 1)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteColumn
        H N hN beta hbeta A target source ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteAsymptoticFixedRightBound
        H beta target source := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteColumn
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteAsymptoticFixedRightBound
  apply Finset.sum_le_sum
  intro mid _hmid
  exact
    mul_le_mul_of_nonneg_left
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_le_asymptoticFixedRightBound
        H N hN beta hbeta hCard hEligibleRowLtOne A source mid)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1GreenWeight_nonneg
        H beta hbeta hThreshold target mid)

/-- The local Green response to the actual remote forcing is controlled by a
configuration-independent, scan-depth-free fixed-right weighted kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackPartialResolvent_remoteForcing_le_asymptoticFixedRightWeightedBound
    (H N M : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hThreshold :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta <
        1)
    (hCard : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (hEligibleRowLtOne :
      (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta) < 1)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (w : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hwNonneg : ∀ source, 0 ≤ w source)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    finiteNonnegativeKernelPartialResolvent
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackKernel
          H beta hbeta).influence
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftRemotePerturbationForcing
          H N hN beta hbeta A w)
        M target ≤
      ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteAsymptoticFixedRightBound
            H beta target source *
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
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteAsymptoticFixedRightBound
            H beta target source *
          w source := by
      apply Finset.sum_le_sum
      intro source _hsource
      exact
        mul_le_mul_of_nonneg_right
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteColumn_le_asymptoticFixedRightBound
            H N hN beta hbeta hThreshold hCard hEligibleRowLtOne A target source)
          (hwNonneg source)

/-- Singleton physical-envelope comparison with both finite propagation
remainders separated: the direct local term is geometric in target/source
distance, the remote term is scan-depth-free, and only the local Green power
remainder depends on M. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeft_singleton_localGeometric_add_asymptoticFixedRightWeightedRemoteBound_add_remainder
    (H N D M : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hThreshold :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta <
        1)
    (hCard : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (hEligibleRowLtOne :
      (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta) < 1)
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
              w t) :
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
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteAsymptoticFixedRightBound
              H beta target s *
            w s) +
        (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta) ^ M * distanceBound := by
  have hBase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeft_singleton_localGeometric_add_weightedRemoteConvolution_add_remainder
      H N D M hN beta hbeta hThreshold A source target hDistance
      amplitude hAmplitude w hwNonneg distanceBound hDistanceBound hwBound hComparison
  have hRemoteSum :
      (∑ s : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteColumn
            H N hN beta hbeta A target s *
          w s) ≤
        ∑ s : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteAsymptoticFixedRightBound
              H beta target s *
            w s := by
    apply Finset.sum_le_sum
    intro s _hs
    exact
      mul_le_mul_of_nonneg_right
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteColumn_le_asymptoticFixedRightBound
          H N hN beta hbeta hThreshold hCard hEligibleRowLtOne A target s)
        (hwNonneg s)
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
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalGreenWeightedRemoteAsymptoticFixedRightBound
              H beta target s *
            w s) +
        (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta) ^ M * distanceBound := by
      linarith

end

end MathlibAnalytic
end MGAP4D
