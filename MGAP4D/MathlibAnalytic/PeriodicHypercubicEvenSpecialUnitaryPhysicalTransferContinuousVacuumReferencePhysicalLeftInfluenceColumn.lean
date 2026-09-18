import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftLocalResidual
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSliceActiveNeighborResidualColumnBound
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance physicalLeftInfluenceColumnSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalLeftInfluenceColumnSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- The older distinct-background coefficient and the canonical Harnack
influence from PR #4472 are definitionally the same scalar. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence_eq_backgroundUpdateHarnackInfluence
    (beta : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
        beta =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta := by
  rfl

/-- Actual bounded-test difference at physical target/source coordinates for
one fixed background pair u,v and one target-indexed test family. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftBoundedTestInfluence
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (phi : PeriodicHypercubicEvenSpatialSliceLink H →
      Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  |(∫ g, phi target g
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B source distinguishedSource target k g₂
        (Function.update A source u)) -
    (∫ g, phi target g
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B source distinguishedSource target k g₂
        (Function.update A source v))|

/-- The actual physical bounded-test influence is pointwise controlled by the
intrinsic active-neighbor Harnack coefficient plus the source-aligned remote
vacuum residual. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftBoundedTestInfluence_le_activeHarnack_add_remoteResidual
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (phi : PeriodicHypercubicEvenSpatialSliceLink H →
      Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : ∀ target, StronglyMeasurable (phi target))
    (hphiBound : ∀ target g, |phi target g| ≤ 1)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftBoundedTestInfluence
        H N hN beta hbeta B A distinguishedSource k g₂ u v phi target source ≤
      (if target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source then
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta
      else 0) +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual
        H N hN beta hbeta A source source target := by
  have hPoint :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_physicalLeft_boundedTest_difference_le_active_add_remoteResidual
      H N hN beta hbeta B A source distinguishedSource target
      k g₂ u v (phi target) (hphi target) (hphiBound target)
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftBoundedTestInfluence,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence_eq_backgroundUpdateHarnackInfluence] using
    hPoint

/-- The finite physical target column of actual bounded-test influence is
bounded by eighteen times the local Harnack coefficient plus the complete
source-aligned remote residual column. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftBoundedTestInfluence_columnSum_le_eighteen_mul_add_remoteResidual
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (phi : PeriodicHypercubicEvenSpatialSliceLink H →
      Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : ∀ target, StronglyMeasurable (phi target))
    (hphiBound : ∀ target g, |phi target g| ≤ 1)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftBoundedTestInfluence
        H N hN beta hbeta B A distinguishedSource k g₂ u v phi target source) ≤
      18 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta +
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual
          H N hN beta hbeta A source source target := by
  let influence :=
    fun target source' : PeriodicHypercubicEvenSpatialSliceLink H =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftBoundedTestInfluence
        H N hN beta hbeta B A distinguishedSource k g₂ u v phi target source'
  let residual :=
    fun target source' : PeriodicHypercubicEvenSpatialSliceLink H =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual
        H N hN beta hbeta A source' source' target
  have hEta :
      0 ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_nonneg
      beta hbeta
  have hResidual : ∀ target source',
      0 ≤ residual target source' := by
    intro target source'
    dsimp [residual]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual_nonneg
        H N hN beta hbeta A source' source' target
  have hPointwise : ∀ target source',
      influence target source' ≤
        (if target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source' then
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta
        else 0) + residual target source' := by
    intro target source'
    dsimp [influence, residual]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftBoundedTestInfluence_le_activeHarnack_add_remoteResidual
        H N hN beta hbeta B A distinguishedSource k g₂ u v phi
        hphi hphiBound target source'
  simpa [influence, residual] using
    periodicHypercubicEvenSpatialSlice_influenceColumnSum_le_eighteen_mul_add_residual
      H influence residual
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta)
      hEta hResidual hPointwise source

/-- The actual physical bounded-test source column is bounded by a concrete
18-neighbor local term plus the arbitrary-step aggregate remote transport.
This is a finite-volume physical conditional-law column estimate; it does not
assert that the scalar right-hand side is below one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftBoundedTestInfluence_columnSum_le_eighteen_mul_add_exp_sixteen_mul_nStepAggregate
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (phi : PeriodicHypercubicEvenSpatialSliceLink H →
      Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : ∀ target, StronglyMeasurable (phi target))
    (hphiBound : ∀ target g, |phi target g| ≤ 1)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (n : ℕ) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftBoundedTestInfluence
        H N hN beta hbeta B A distinguishedSource k g₂ u v phi target source) ≤
      18 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta +
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
  have hLocal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftBoundedTestInfluence_columnSum_le_eighteen_mul_add_remoteResidual
      H N hN beta hbeta B A distinguishedSource k g₂ u v phi
      hphi hphiBound source
  have hRemote :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual_columnSum_le_exp_sixteen_mul_nStepAggregate
      H N hN beta hbeta A source source n
  exact hLocal.trans (by
    simpa [add_comm] using
      add_le_add_right hRemote
        (18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta))

end

end MathlibAnalytic
end MGAP4D
