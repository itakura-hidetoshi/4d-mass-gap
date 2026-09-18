import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceRemotePhysicalInfluenceResidual
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberOffFiberConditionalLaw
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance physicalLeftLocalResidualSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalLeftLocalResidualSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- If the distinguished C5 target is chosen to be the physical source itself,
the remote target set is exactly the off-diagonal complement of the intrinsic
spatial active-neighbor set. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers_self_mem_iff
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
    periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers,
    periodicHypercubicEvenSpatialSlice_mem_activeNeighbors_iff]

/-- Actual physical left-background influence splits into a local active-neighbor
term plus the new remote vacuum residual.

The literal one-link law uses the physical source itself as the distinguished
C5 target.  Three cases are kept separate:
* diagonal source = target: exact base-fiber invariance gives zero;
* direct active neighbor: the existing distinct-background conditional-law
  Harnack coefficient is used only on this sparse set;
* nonactive off-diagonal target: the #4469 remote physical residual applies.

Thus the old dense coefficient is not reinterpreted as sparse; it is restricted
to the geometry on which the local term is explicitly supported. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_physicalLeft_boundedTest_difference_le_active_add_remoteResidual
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedSource target : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : StronglyMeasurable phi) (hphiBound : ∀ g, |phi g| ≤ 1) :
    |(∫ g, phi g ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B source distinguishedSource target k g₂
        (Function.update A source u)) -
      (∫ g, phi g ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B source distinguishedSource target k g₂
        (Function.update A source v))| ≤
      (if target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source then
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta
      else 0) +
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual
        H N hN beta hbeta A source source target := by
  classical
  by_cases hEq : target = source
  · subst target
    have hU :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_update_fiber
        H N hN beta hbeta B source distinguishedSource source k g₂ A u
    have hV :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_update_fiber
        H N hN beta hbeta B source distinguishedSource source k g₂ A v
    rw [hU, hV]
    have hResidual :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual_nonneg
        H N hN beta hbeta A source source source
    have hNotActive :
        source ∉ periodicHypercubicEvenSpatialSliceActiveNeighbors H source := by
      simp [periodicHypercubicEvenSpatialSlice_mem_activeNeighbors_iff]
    simpa [hNotActive] using hResidual
  · by_cases hActive :
        target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source
    · have hLocal :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_boundedTest_influence_update_distinct_background
          H N hN beta hbeta B source distinguishedSource target source
          (Ne.symm hEq) k g₂ A u v phi hphi hphiBound
      have hLocal' :
          |(∫ g, phi g ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
              H N hN beta hbeta B source distinguishedSource target k g₂
              (Function.update A source u)) -
            (∫ g, phi g ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
              H N hN beta hbeta B source distinguishedSource target k g₂
              (Function.update A source v))| ≤
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
              beta := by
        simpa [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence] using
          hLocal
      have hResidual :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual_nonneg
          H N hN beta hbeta A source source target
      exact hLocal'.trans (by
        simpa [hActive] using
          (le_add_of_nonneg_right hResidual :
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence beta ≤
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence beta +
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual
                  H N hN beta hbeta A source source target))
    · have hRemote :
          target ∈
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
              H source source := by
        exact
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers_self_mem_iff
            H source target).2 ⟨hEq, hActive⟩
      have hRemoteBound :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_remote_boundedTest_difference_le_physicalResidual
          H N hN beta hbeta B A source source distinguishedSource target
          hRemote k g₂ u v phi hphi hphiBound
      simpa [hActive] using hRemoteBound

end

end MathlibAnalytic
end MGAP4D
