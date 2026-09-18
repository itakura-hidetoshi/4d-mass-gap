import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceRemoteBoundedTestInfluenceColumn
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance remotePhysicalInfluenceResidualSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance remotePhysicalInfluenceResidualSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- The targetwise worst-case cross-ratio majorant is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant_nonneg
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
      H N hN beta hbeta A target source := by
  have hChosen :
      0 ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorant
        H N hN beta hbeta A target source 1 1 1 1 := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorant
    exact
      finitePositiveWeightCrossRatioInfluenceTransform_nonneg _
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioRadius_nonneg
          H N hN beta hbeta A target source 1 1 1 1)
  exact hChosen.trans
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioCrossRatioInfluenceMajorant_le_worstCase
      H N hN beta hbeta A target source 1 1 1 1)

/-- A concrete remote residual kernel: use the proved worst-case actual
conditional-law majorant exactly on the C5 remote target set and zero on the
geometric exceptional set.

The distinguished target remains explicit.  This definition therefore does
not erase the extra C5 bookkeeping exception or identify it with the intrinsic
18-neighbor sparse carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedTarget target : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  if target ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
        H source distinguishedTarget then
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
      H N hN beta hbeta A target source
  else 0

/-- The concrete remote residual is pointwise nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual_nonneg
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedTarget target : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual
      H N hN beta hbeta A source distinguishedTarget target := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual
  split_ifs
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant_nonneg
        H N hN beta hbeta A target source
  · exact le_rfl

/-- On a C5-remote target, the actual source-updated one-link conditional laws
are controlled by the concrete residual kernel for every bounded strongly
measurable real test. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_remote_boundedTest_difference_le_physicalResidual
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedTarget distinguishedSource target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRemote : target ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
      H source distinguishedTarget)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : StronglyMeasurable phi) (hphiBound : ∀ g, |phi g| ≤ 1) :
    |(∫ g, phi g ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B distinguishedTarget distinguishedSource target k g₂
        (Function.update A source u)) -
      (∫ g, phi g ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B distinguishedTarget distinguishedSource target k g₂
        (Function.update A source v))| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual
        H N hN beta hbeta A source distinguishedTarget target := by
  classical
  have hNotExceptional :
      target ∉ periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
        H source distinguishedTarget := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers] using
      hRemote
  rcases
    periodicHypercubicEvenSpatialSlice_not_mem_C5ExceptionalBackgroundFibers
      H source distinguishedTarget target hNotExceptional with
    ⟨hSourceTarget, hTargetDistinguished, hNoShare⟩
  have hBound :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_remote_boundedTest_integral_difference_abs_le_worstCaseCrossRatioInfluenceMajorant
      H N hN beta hbeta B
      distinguishedTarget distinguishedSource target source
      hTargetDistinguished hSourceTarget hNoShare
      k g₂ u v A phi hphi hphiBound
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual,
    hRemote] using hBound

/-- Summing the concrete residual over all physical targets is exactly the
already-merged targetwise worst-case remote cross-ratio column. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual_columnSum_eq_worstCaseRemoteColumn
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual
        H N hN beta hbeta A source distinguishedTarget target) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseRemoteCrossRatioInfluenceColumn
        H N hN beta hbeta A source distinguishedTarget := by
  classical
  let remote :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
      H source distinguishedTarget
  let q := fun target : PeriodicHypercubicEvenSpatialSliceLink H =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
      H N hN beta hbeta A target source
  change (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      if target ∈ remote then q target else 0) =
    ∑ target ∈ remote, q target
  rw [← Finset.sum_filter]
  have hFilter :
      (Finset.univ.filter fun target : PeriodicHypercubicEvenSpatialSliceLink H =>
        target ∈ remote) = remote := by
    ext target
    simp
  rw [hFilter]

/-- The concrete remote residual column is bounded by the same arbitrary-step
aggregate tagged transport as the worst-case cross-ratio column. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual_columnSum_le_exp_sixteen_mul_nStepAggregate
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H)
    (n : ℕ) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual
        H N hN beta hbeta A source distinguishedTarget target) ≤
      Real.exp (16 * beta) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation
              H beta source distinguishedTarget)
            n (Sum.inr source) +
          2 * ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
              H beta hbeta
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation
                H beta source distinguishedTarget)
              n (Sum.inl e)) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual_columnSum_eq_worstCaseRemoteColumn]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseRemoteCrossRatioInfluenceColumn_le_exp_sixteen_mul_nStepAggregateRight_add_two_mul_leftVariationTotal
      H N hN beta hbeta A source distinguishedTarget n

end

end MathlibAnalytic
end MGAP4D
