import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairTargetResidualVacuumSum
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointCanonicalResidualSweepStageLocalProfile
import Mathlib.Tactic

/-!
# Sweep-stage representatives feed the global response-energy bound

PR #4846 turns the fixed-background pin-free Schur estimate into a global
physical-vacuum bound by a finite sum of genuine target fiber variances.

PR #4770 already supplies, for each spatial link, a bounded concrete
representative at the canonical sweep stage whose canonical residual L2 norm
is bounded by the existing six-spatial local profile with coefficient one.

This file chooses those representatives simultaneously across the finite link
set and proves

  sum_target CanonicalFiberVariance(target,F_target)
    <= ofReal(sum_target localProfile(target)^2).

It then feeds that exact stagewise family into the PR #4846 response-energy
bound.  No finite-cardinality factor is introduced: the only finite operation
is a pointwise sum of coefficient-one squared residual estimates.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance sweepStageResponseEnergySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Simultaneously choose the PR #4770 bounded sweep-stage representative for
every spatial link.  The sum of the resulting canonical target fiber
variances is bounded with coefficient one by the existing six-spatial local
profile energy. -/
theorem
    exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_linkIndexedRepresentatives_canonicalFiberVariance_sum_le_localProfile_sq_sum_ofReal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    ∃
      (F :
        PeriodicHypercubicEvenSpatialSliceLink H →
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : ∀ e, StronglyMeasurable (F e))
      (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
      (hbound : ∀ e z, ‖F e z‖ ≤ bound e),
      (∀ e,
        ∃ pre :
          List
            (PeriodicHypercubicEvenFixedSpatialColorLink H
              (periodicHypercubicEvenSpatialSliceLinkColor H e)),
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta
              (F e) (hF e) (bound e) (hbound e) =
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
              H N hN beta hbeta
              (periodicHypercubicEvenSpatialSliceLinkColor H e) pre f) ∧
      (∀ e,
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
            H N hN beta hbeta e
            (F e) (hF e) (bound e) (hbound e)‖ ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
            H N hN beta hbeta f e) ∧
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
          H N hN beta hbeta e (F e)) ≤
        ENNReal.ofReal
          (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
              H N hN beta hbeta f e ^ 2) := by
  classical
  have hWitness :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ∃
          (pre :
            List
              (PeriodicHypercubicEvenFixedSpatialColorLink H
                (periodicHypercubicEvenSpatialSliceLinkColor H e)))
          (F :
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
          (hF : StronglyMeasurable F)
          (bound : ℝ)
          (hbound : ∀ z, ‖F z‖ ≤ bound),
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound =
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
              H N hN beta hbeta
              (periodicHypercubicEvenSpatialSliceLinkColor H e) pre f ∧
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
              H N hN beta hbeta e F hF bound hbound‖ ≤
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
              H N hN beta hbeta f e := by
    intro e
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_exists_boundedRepresentative_canonicalResidualL2_norm_le_localProfile
        H N hN beta hbeta e f hf
  choose pre F hF bound hbound hBoth using hWitness
  have hRep :
      ∀ e,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta
            (F e) (hF e) (bound e) (hbound e) =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
            H N hN beta hbeta
            (periodicHypercubicEvenSpatialSliceLinkColor H e) (pre e) f := by
    intro e
    exact (hBoth e).1
  have hLocal :
      ∀ e,
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
            H N hN beta hbeta e
            (F e) (hF e) (bound e) (hbound e)‖ ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
            H N hN beta hbeta f e := by
    intro e
    exact (hBoth e).2
  refine ⟨F, hF, bound, hbound, ?_, hLocal, ?_⟩
  · intro e
    exact ⟨pre e, hRep e⟩
  · have hEach :
        ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
              H N hN beta hbeta e (F e) ≤
            ENNReal.ofReal
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
                H N hN beta hbeta f e ^ 2) := by
      intro e
      have hLocal0 :
          0 ≤
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
              H N hN beta hbeta f e :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_nonneg
          H N hN beta hbeta f e
      have hSq :
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
              H N hN beta hbeta e
              (F e) (hF e) (bound e) (hbound e)‖ ^ 2 ≤
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
              H N hN beta hbeta f e ^ 2 :=
        (sq_le_sq₀
          (norm_nonneg _)
          hLocal0).2 (hLocal e)
      calc
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
            H N hN beta hbeta e (F e) =
          ENNReal.ofReal
            (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2
                H N hN beta hbeta e
                (F e) (hF e) (bound e) (hbound e)‖ ^ 2) := by
              symm
              exact
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberMeanResidualL2_norm_sq_ofReal_eq_variance
                  H N hN beta hbeta e
                  (F e) (hF e) (bound e) (hbound e)
        _ ≤
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
              H N hN beta hbeta f e ^ 2) :=
          ENNReal.ofReal_le_ofReal hSq
    calc
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkCanonicalFiberVarianceFunctional
          H N hN beta hbeta e (F e)) ≤
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
              H N hN beta hbeta f e ^ 2) := by
          exact Finset.sum_le_sum (fun e _ => hEach e)
      _ =
        ENNReal.ofReal
          (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
              H N hN beta hbeta f e ^ 2) := by
          symm
          simpa using
            (ENNReal.ofReal_sum_of_nonneg
              (s := (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)))
              (f := fun e =>
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
                  H N hN beta hbeta f e ^ 2)
              (fun e _ => sq_nonneg _))

/-- The simultaneous sweep-stage representatives from the previous theorem
feed directly into the global response-amplitude estimate of PR #4846. -/
theorem
    exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_linkIndexedRepresentatives_responseAmplitude_vacuum_lintegral_le_responseResidualCoefficient_mul_localProfile_sq_sum_ofReal
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
          s hs)
    (H : ℕ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    ∃
      (F :
        PeriodicHypercubicEvenSpatialSliceLink H →
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : ∀ e, StronglyMeasurable (F e))
      (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
      (hbound : ∀ e z, ‖F e z‖ ≤ bound e),
      (∀ e,
        ∃ pre :
          List
            (PeriodicHypercubicEvenFixedSpatialColorLink H
              (periodicHypercubicEvenSpatialSliceLinkColor H e)),
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta
              (F e) (hF e) (bound e) (hbound e) =
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
              H N hN beta hbeta
              (periodicHypercubicEvenSpatialSliceLinkColor H e) pre f) ∧
      (∫⁻ C,
        ENNReal.ofReal
          (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
                H N hN beta hbeta C distinguishedSource
                (F target) (hF target) (bound target) (hbound target)
                source target) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
            s beta *
          ENNReal.ofReal
            (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
                H N hN beta hbeta f e ^ 2) := by
  rcases
      exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_linkIndexedRepresentatives_canonicalFiberVariance_sum_le_localProfile_sq_sum_ofReal
        H N hN beta hbeta f hf with
    ⟨F, hF, bound, hbound, hRep, hLocal, hVariance⟩
  refine ⟨F, hF, bound, hbound, hRep, ?_⟩
  have hResponse :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairLinkIndexedFixedBackgroundResponseAmplitude_vacuum_lintegral_le_responseResidualCoefficient_mul_canonicalFiberVarianceFunctional_sum
      N hN s hs beta hbeta hcut H distinguishedSource
      F hF bound hbound
  exact hResponse.trans
    (mul_le_mul_left'
      hVariance
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
        s beta))

end

end MGAP4D.MathlibAnalytic
