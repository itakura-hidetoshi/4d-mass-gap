import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceRemotePhysicalInfluenceResidual
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSliceActiveNeighborResidualColumnBound
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance sourceAlignedRemoteResidualSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance sourceAlignedRemoteResidualSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- When the distinguished C5 target is chosen to be the physical source
itself, the exceptional background set loses the extra bookkeeping point and
is exactly the source together with its intrinsic active-neighbor set. -/
theorem
    periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers_source_eq_insert_activeNeighbors
    (H : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
        H source source =
      insert source
        (periodicHypercubicEvenSpatialSliceActiveNeighbors H source) := by
  classical
  simp [periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers]

/-- In the source-aligned specialization, C5-remote targets are exactly the
off-diagonal links outside the intrinsic active-neighbor set. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReference_mem_C5RemoteTargetFibers_source_iff
    (H : ℕ)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H) :
    target ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
          H source source ↔
      target ≠ source ∧
        target ∉ periodicHypercubicEvenSpatialSliceActiveNeighbors H source := by
  classical
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers,
    periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers]

/-- Source-aligned form of the concrete remote physical residual.  This is the
same residual from the preceding theorem unit, specialized so that its zero
set contains exactly the diagonal and the intrinsic active-neighbor region. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual
    H N hN beta hbeta A source source target

/-- The source-aligned residual is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_nonneg
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
      H N hN beta hbeta A source target := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual_nonneg
      H N hN beta hbeta A source source target

/-- The source-aligned residual vanishes on the diagonal. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_self
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
      H N hN beta hbeta A source source = 0 := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers,
    periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers]

/-- The source-aligned residual also vanishes on every intrinsic active
neighbor; all such local terms remain reserved for the separate sparse local
coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_eq_zero_of_active
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hActive : target ∈
      periodicHypercubicEvenSpatialSliceActiveNeighbors H source) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
      H N hN beta hbeta A source target = 0 := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual
  have hNotRemote :
      target ∉
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
          H source source := by
    intro hRemote
    have hData :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReference_mem_C5RemoteTargetFibers_source_iff
        H source target).mp hRemote
    exact hData.2 hActive
  simp [hNotRemote]

/-- Outside the diagonal and intrinsic active-neighbor set, the source-aligned
residual is exactly the targetwise worst-case cross-ratio influence majorant. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_eq_worstCase_of_remote
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (hNotActive : target ∉
      periodicHypercubicEvenSpatialSliceActiveNeighbors H source) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
        H N hN beta hbeta A source target =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
        H N hN beta hbeta A target source := by
  classical
  have hRemote :
      target ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
          H source source :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReference_mem_C5RemoteTargetFibers_source_iff
      H source target).mpr ⟨hne, hNotActive⟩
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual,
    hRemote]

/-- For an off-diagonal non-active target, the actual source-updated one-link
conditional laws are controlled by the source-aligned remote residual for every
bounded strongly measurable real test. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_sourceAlignedRemote_boundedTest_difference_le_residual
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedSource target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (hNotActive : target ∉ periodicHypercubicEvenSpatialSliceActiveNeighbors H source)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : StronglyMeasurable phi) (hphiBound : ∀ g, |phi g| ≤ 1) :
    |(∫ g, phi g ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B source distinguishedSource target k g₂
        (Function.update A source u)) -
      (∫ g, phi g ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B source distinguishedSource target k g₂
        (Function.update A source v))| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
        H N hN beta hbeta A source target := by
  have hRemote :
      target ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
          H source source :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReference_mem_C5RemoteTargetFibers_source_iff
      H source target).mpr ⟨hne, hNotActive⟩
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_remote_boundedTest_difference_le_physicalResidual
      H N hN beta hbeta B A
      source source distinguishedSource target hRemote
      k g₂ u v phi hphi hphiBound

/-- The entire source-aligned residual column is exactly the existing remote
worst-case column with distinguished target specialized to the source. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_columnSum_eq_worstCaseRemoteColumn
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
        H N hN beta hbeta A source target) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseRemoteCrossRatioInfluenceColumn
        H N hN beta hbeta A source source := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual_columnSum_eq_worstCaseRemoteColumn
      H N hN beta hbeta A source source

/-- The source-aligned residual column therefore inherits the same arbitrary-step
aggregate tagged transport bound, now with no extra distinguished-target point
outside the intrinsic diagonal-plus-active-neighbor geometry. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_columnSum_le_exp_sixteen_mul_nStepAggregate
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (n : ℕ) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
        H N hN beta hbeta A source target) ≤
      Real.exp (16 * beta) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation
              H beta source source)
            n (Sum.inr source) +
          2 * ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
              H beta hbeta
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioRemoteAggregateVariation
                H beta source source)
              n (Sum.inl e)) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual_columnSum_le_exp_sixteen_mul_nStepAggregate
      H N hN beta hbeta A source source n

end

end MathlibAnalytic
end MGAP4D
