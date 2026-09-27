import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFullResponseExactStageResidual
import Mathlib.Tactic

/-!
# Exact canonical stage-residual energy and sweep path loss

PR #4856 identifies each canonical one-link sweep local profile with the norm
of the actual Hilbert residual at the preserved canonical prefix. PR #4857
charges the complete target-law response energy directly to the sum of the
squared norms of those stage residuals.

This file identifies that entire stage-residual energy exactly with the
already-established six-spatial one-link sweep path loss:

  (1/6) * sum_e ||stageResidual_e||^2 = sweepPathLoss(f).

Consequently

  sum_e ||stageResidual_e||^2 = 6 * sweepPathLoss(f),

and the response-energy estimate can be sharpened from the six-spatial
residual-energy majorant to the exact ordered sweep path-loss carrier.

No new analytic estimate, probability law, response coefficient, target
reordering, or finite-cardinality factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance stageResidualPathLossSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- For any preserved canonical-prefix family, the normalized sum of squared
actual stage-residual norms is exactly the six-spatial one-link sweep path
loss. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_canonicalPrefix_stageResidual_normalized_sq_sum_eq_sweepPathLoss
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (pre suffix :
      (e : PeriodicHypercubicEvenSpatialSliceLink H) →
        List
          (PeriodicHypercubicEvenFixedSpatialColorLink H
            (periodicHypercubicEvenSpatialSliceLinkColor H e)))
    (hSplit :
      ∀ e,
        (Finset.univ :
          Finset
            (PeriodicHypercubicEvenFixedSpatialColorLink H
              (periodicHypercubicEvenSpatialSliceLinkColor H e))).toList =
          pre e ++
            (⟨e, rfl⟩ :
              PeriodicHypercubicEvenFixedSpatialColorLink H
                (periodicHypercubicEvenSpatialSliceLinkColor H e)) ::
              suffix e)
    (hFresh :
      ∀ e,
        (⟨e, rfl⟩ :
          PeriodicHypercubicEvenFixedSpatialColorLink H
            (periodicHypercubicEvenSpatialSliceLinkColor H e)) ∉ pre e) :
    (1 / 6 : ℝ) *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          norm
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkCanonicalStageResidualVector
              H N hN beta hbeta e (pre e) f) ^ 2 =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
        H N hN beta hbeta f := by
  have hSum :
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        norm
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkCanonicalStageResidualVector
            H N hN beta hbeta e (pre e) f) ^ 2) =
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
            H N hN beta hbeta f e ^ 2 := by
    apply Finset.sum_congr rfl
    intro e he
    have hProfile :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_eq_stageResidual_norm_of_canonicalPrefix
        H N hN beta hbeta e (pre e) (suffix e) f
        (hSplit e) (hFresh e)
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkCanonicalStageResidualVector]
      using congrArg (fun x : ℝ => x ^ 2) hProfile.symm
  rw [hSum]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_normalized_sq_sum_eq_sweepPathLoss
      H N hN beta hbeta f

/-- Unnormalized exact form of the preceding identity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_canonicalPrefix_stageResidual_sq_sum_eq_six_mul_sweepPathLoss
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (pre suffix :
      (e : PeriodicHypercubicEvenSpatialSliceLink H) →
        List
          (PeriodicHypercubicEvenFixedSpatialColorLink H
            (periodicHypercubicEvenSpatialSliceLinkColor H e)))
    (hSplit :
      ∀ e,
        (Finset.univ :
          Finset
            (PeriodicHypercubicEvenFixedSpatialColorLink H
              (periodicHypercubicEvenSpatialSliceLinkColor H e))).toList =
          pre e ++
            (⟨e, rfl⟩ :
              PeriodicHypercubicEvenFixedSpatialColorLink H
                (periodicHypercubicEvenSpatialSliceLinkColor H e)) ::
              suffix e)
    (hFresh :
      ∀ e,
        (⟨e, rfl⟩ :
          PeriodicHypercubicEvenFixedSpatialColorLink H
            (periodicHypercubicEvenSpatialSliceLinkColor H e)) ∉ pre e) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      norm
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkCanonicalStageResidualVector
          H N hN beta hbeta e (pre e) f) ^ 2) =
      6 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
          H N hN beta hbeta f := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_canonicalPrefix_stageResidual_normalized_sq_sum_eq_sweepPathLoss
      H N hN beta hbeta f pre suffix hSplit hFresh
  linarith

/-- The exact stage-residual energy is controlled by the genuine six-spatial
residual energy with only the fixed six-color normalization. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_canonicalPrefix_stageResidual_sq_sum_le_six_mul_residualEnergy
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (pre suffix :
      (e : PeriodicHypercubicEvenSpatialSliceLink H) →
        List
          (PeriodicHypercubicEvenFixedSpatialColorLink H
            (periodicHypercubicEvenSpatialSliceLinkColor H e)))
    (hSplit :
      ∀ e,
        (Finset.univ :
          Finset
            (PeriodicHypercubicEvenFixedSpatialColorLink H
              (periodicHypercubicEvenSpatialSliceLinkColor H e))).toList =
          pre e ++
            (⟨e, rfl⟩ :
              PeriodicHypercubicEvenFixedSpatialColorLink H
                (periodicHypercubicEvenSpatialSliceLinkColor H e)) ::
              suffix e)
    (hFresh :
      ∀ e,
        (⟨e, rfl⟩ :
          PeriodicHypercubicEvenFixedSpatialColorLink H
            (periodicHypercubicEvenSpatialSliceLinkColor H e)) ∉ pre e) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      norm
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkCanonicalStageResidualVector
          H N hN beta hbeta e (pre e) f) ^ 2) ≤
      6 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
          H N hN beta hbeta f := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_canonicalPrefix_stageResidual_sq_sum_eq_six_mul_sweepPathLoss
      H N hN beta hbeta f pre suffix hSplit hFresh]
  exact
    mul_le_mul_of_nonneg_left
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss_le_residualEnergy
        H N hN beta hbeta f)
      (by norm_num)

/-- Choose the canonical-prefix family so that the actual full response energy
is charged to the exact ordered one-link sweep path loss. -/
theorem
    exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_linkIndexedRepresentatives_fullResponseL2Sum_vacuum_lintegral_le_responseResidualCoefficient_mul_sixSweepPathLoss_ofReal
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
      (pre suffix :
        (e : PeriodicHypercubicEvenSpatialSliceLink H) →
          List
            (PeriodicHypercubicEvenFixedSpatialColorLink H
              (periodicHypercubicEvenSpatialSliceLinkColor H e)))
      (F :
        PeriodicHypercubicEvenSpatialSliceLink H →
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : ∀ e, StronglyMeasurable (F e))
      (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
      (hbound : ∀ e z, ‖F e z‖ ≤ bound e),
      (∀ e,
        (Finset.univ :
          Finset
            (PeriodicHypercubicEvenFixedSpatialColorLink H
              (periodicHypercubicEvenSpatialSliceLinkColor H e))).toList =
            pre e ++
              (⟨e, rfl⟩ :
                PeriodicHypercubicEvenFixedSpatialColorLink H
                  (periodicHypercubicEvenSpatialSliceLinkColor H e)) ::
                suffix e) ∧
      (∀ e,
        (⟨e, rfl⟩ :
          PeriodicHypercubicEvenFixedSpatialColorLink H
            (periodicHypercubicEvenSpatialSliceLinkColor H e)) ∉ pre e) ∧
      (∀ e,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta
            (F e) (hF e) (bound e) (hbound e) =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
            H N hN beta hbeta
            (periodicHypercubicEvenSpatialSliceLinkColor H e)
            (pre e) f) ∧
      (∫⁻ C,
        ENNReal.ofReal
          (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            norm
              (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
                  H N hN beta hbeta C distinguishedSource source target
                  (C distinguishedSource) (C source)
                  (F target) (hF target) (bound target) (hbound target) C 0) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
            s beta *
          ENNReal.ofReal
            (6 *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
                H N hN beta hbeta f) := by
  rcases
      exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_linkIndexedRepresentatives_fullResponseL2Sum_vacuum_lintegral_le_responseResidualCoefficient_mul_stageResidual_norm_sq_sum_ofReal
        N hN s hs beta hbeta hcut H distinguishedSource f hf with
    ⟨pre, suffix, F, hF, bound, hbound,
      hSplit, hFresh, hRep, hResponse⟩
  refine
    ⟨pre, suffix, F, hF, bound, hbound,
      hSplit, hFresh, hRep, ?_⟩
  have hStageEq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_canonicalPrefix_stageResidual_sq_sum_eq_six_mul_sweepPathLoss
      H N hN beta hbeta f pre suffix hSplit hFresh
  rw [hStageEq] at hResponse
  exact hResponse

end

end MGAP4D.MathlibAnalytic
