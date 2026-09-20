import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioAuxiliaryResolvent
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTargetWorstCaseCrossRatioInfluenceMajorant
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance fixedRightFullResponseResolventSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Under the explicit fixed-volume strict eligible-row criterion, the total
physical-left variation of the singleton fixed-right target-ratio profile
contracts geometrically under the actual tagged restricted random scan. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_taggedRestrictedRandomScan_leftTotal_le_explicitEligibleRow_rate_pow_mul
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hCard : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (hEligibleRowLtOne :
      (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta) < 1)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (n : ℕ) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
          H beta target)
        n (Sum.inl e)) ≤
      finiteInfluenceKernelReciprocalRandomScanRate
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
              beta) ^ n *
        Real.exp (16 * beta) := by
  classical
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
      H beta hbeta
  let embedding :
      PeriodicHypercubicEvenSpatialSliceLink H →
        Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H) :=
    fun fiber => Sum.inl fiber
  let physicalVariation :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
      H beta target
  let initial :
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation
      H physicalVariation
  let rowCoefficient : ℝ :=
    (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
        beta)
  have hEmbedding : Function.Injective embedding := by
    intro a b hab
    exact Sum.inl.inj hab
  have hRowNonneg : 0 ≤ rowCoefficient := by
    dsimp [rowCoefficient]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedEligiblePullback_rowCoefficient_nonneg
        H beta hbeta
  have hRowSum :
      ∀ t : PeriodicHypercubicEvenSpatialSliceLink H,
        finiteInfluenceKernelRowSum
          (finiteInfluenceKernelRestrictedTargetPullback K embedding) t ≤
            rowCoefficient := by
    intro t
    dsimp [K, embedding, rowCoefficient]
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedEligiblePullback_rowSum_eq
        H beta hbeta t]
  have hInitialNonneg : ∀ e, 0 ≤ initial e := by
    intro e
    cases e with
    | inl e =>
        dsimp [initial]
        simpa [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_nonneg
            H beta target e
    | inr e =>
        simp [initial,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation]
  have hBase :=
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_eligibleTotal_le_rate_pow_mul
      K embedding hEmbedding hCard rowCoefficient hRowNonneg hRowSum
      initial hInitialNonneg n
  have hInitialTotal :
      (∑ t : PeriodicHypercubicEvenSpatialSliceLink H, initial (embedding t)) =
        Real.exp (16 * beta) := by
    calc
      (∑ t : PeriodicHypercubicEvenSpatialSliceLink H, initial (embedding t)) =
          ∑ t : PeriodicHypercubicEvenSpatialSliceLink H, physicalVariation t := by
            apply Finset.sum_congr rfl
            intro t _ht
            simp [initial, embedding,
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation]
      _ = Real.exp (16 * beta) := by
          dsimp [physicalVariation]
          exact
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_sum_eq_exp_sixteen
              H beta target
  rw [hInitialTotal] at hBase
  simpa [
    K,
    embedding,
    initial,
    physicalVariation,
    rowCoefficient,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate] using
    hBase

/-- The complete finite-step fixed-right target response term appearing in the
remote cross-ratio majorant is uniformly controlled by the represented-source
auxiliary resolvent plus the geometrically decaying physical-left total.

This remains a fixed-volume bound because the current coarse left-left tagged
kernel has the explicit volume-dependent row coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_taggedRestrictedRandomScan_rightSource_add_two_leftTotal_le_explicitEligibleRow_resolvent
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hCard : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (hEligibleRowLtOne :
      (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta) < 1)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
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
              n (Sum.inl e) ≤
      (2 *
        (((Real.exp (8 * beta)) ^ 2 - 1) /
          ((Real.exp (8 * beta)) ^ 2 + 1))) *
        (Real.exp (16 * beta) *
          (1 -
            (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
                beta))⁻¹) +
      2 *
        (finiteInfluenceKernelReciprocalRandomScanRate
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
                beta) ^ n *
          Real.exp (16 * beta)) := by
  have hRight :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_taggedRestrictedRandomScan_rightSource_le_explicitEligibleRow_resolvent
      H beta hbeta hCard hEligibleRowLtOne target source n
  have hLeft :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_taggedRestrictedRandomScan_leftTotal_le_explicitEligibleRow_rate_pow_mul
      H beta hbeta hCard hEligibleRowLtOne target n
  exact
    add_le_add hRight
      (mul_le_mul_of_nonneg_left hLeft (by norm_num))

/-- Consequently the targetwise worst-case remote fixed-right cross-ratio
influence majorant is bounded by an explicit finite-volume resolvent envelope
whose only n-dependent term is the geometric eligible-left remainder. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant_le_explicitEligibleRow_resolvent_of_remote
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hCard : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (hEligibleRowLtOne :
      (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
          beta) < 1)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
        H N hN beta hbeta B target source ≤
      Real.exp (16 * beta) *
        ((2 *
          (((Real.exp (8 * beta)) ^ 2 - 1) /
            ((Real.exp (8 * beta)) ^ 2 + 1))) *
          (Real.exp (16 * beta) *
            (1 -
              (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
                  beta))⁻¹) +
        2 *
          (finiteInfluenceKernelReciprocalRandomScanRate
              (PeriodicHypercubicEvenSpatialSliceLink H)
              (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
                  beta) ^ n *
            Real.exp (16 * beta))) := by
  have hBase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant_le_exp_sixteen_mul_nStepTargetBound_of_remote
      H N hN beta hbeta B hne hNoShare n
  have hResponse :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_taggedRestrictedRandomScan_rightSource_add_two_leftTotal_le_explicitEligibleRow_resolvent
      H beta hbeta hCard hEligibleRowLtOne target source n
  exact hBase.trans
    (mul_le_mul_of_nonneg_left hResponse (Real.exp_pos _).le)

end

end MathlibAnalytic
end MGAP4D
