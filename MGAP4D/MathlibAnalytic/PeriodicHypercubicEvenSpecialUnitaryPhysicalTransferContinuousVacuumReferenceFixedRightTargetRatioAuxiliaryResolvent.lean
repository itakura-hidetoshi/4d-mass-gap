import MGAP4D.MathlibAnalytic.FiniteInfluenceKernelRestrictedTargetRandomScanAuxiliaryResolvent
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRemoteKernelSectionRestrictedRandomScanExplicitEligibleRow
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceFixedRightTargetRatioStationaryResidual
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance fixedRightTaggedAuxiliaryResolventSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The exact cross-boundary diagonal C5 coefficient is nonnegative at physical
coupling `beta ≥ 0`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDiagonalCoefficient_nonneg
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    0 ≤
      2 *
        (((Real.exp (8 * beta)) ^ 2 - 1) /
          ((Real.exp (8 * beta)) ^ 2 + 1)) := by
  have hExp : 1 ≤ Real.exp (8 * beta) := by
    apply Real.one_le_exp
    nlinarith
  have hSq : 1 ≤ (Real.exp (8 * beta)) ^ 2 := by
    nlinarith [Real.exp_pos (8 * beta)]
  exact
    mul_nonneg (by norm_num)
      (div_nonneg (sub_nonneg.mpr hSq) (by positivity))

/-- The singleton fixed-right target-ratio variation has total physical-left
mass exactly `exp (16 * beta)`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_sum_eq_exp_sixteen
    (H : ℕ)
    (beta : ℝ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
        H beta target e) =
      Real.exp (16 * beta) := by
  classical
  rw [Finset.sum_eq_single target]
  · simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation]
  · intro e _he hne
    simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation,
      hne]
  · simp

/-- Under the explicit fixed-volume strict eligible-row criterion, the
represented right-source component of the tagged restricted random-scan
transport of the singleton fixed-right target-ratio variation is uniformly
bounded by the cross-boundary diagonal coefficient times the eligible
resolvent.

This is the concrete `Sum.inr source` specialization of the abstract
auxiliary-coordinate resolvent. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_taggedRestrictedRandomScan_rightSource_le_explicitEligibleRow_resolvent
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
        n (Sum.inr source) ≤
      (2 *
        (((Real.exp (8 * beta)) ^ 2 - 1) /
          ((Real.exp (8 * beta)) ^ 2 + 1))) *
        (Real.exp (16 * beta) *
          (1 -
            (((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) - 1 : ℕ) : ℝ) *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
                beta))⁻¹) := by
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
  let auxCoefficient : ℝ :=
    2 *
      (((Real.exp (8 * beta)) ^ 2 - 1) /
        ((Real.exp (8 * beta)) ^ 2 + 1))
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
  have hAux :
      ∀ t : PeriodicHypercubicEvenSpatialSliceLink H,
        (Sum.inr source :
          Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H)) ≠ embedding t := by
    intro t
    simp [embedding]
  have hAuxCoefficientNonneg : 0 ≤ auxCoefficient := by
    dsimp [auxCoefficient]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDiagonalCoefficient_nonneg
        beta hbeta
  have hAuxInfluence :
      ∀ t : PeriodicHypercubicEvenSpatialSliceLink H,
        K.influence (embedding t) (Sum.inr source) ≤ auxCoefficient := by
    intro t
    dsimp [K, embedding]
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel_left_right
        H beta hbeta t source]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
    by_cases hst : source = t
    · simp [hst, auxCoefficient]
    · simp [hst, auxCoefficient, hAuxCoefficientNonneg]
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
  have hInitialAux :
      initial
        (Sum.inr source :
          Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H)) = 0 := by
    simp [initial,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation]
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
  have hBound :=
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_aux_le_resolvent
      K embedding hEmbedding hCard rowCoefficient hRowNonneg hEligibleRowLtOne
      hRowSum
      (Sum.inr source) hAux
      auxCoefficient hAuxCoefficientNonneg hAuxInfluence
      initial hInitialNonneg hInitialAux n
  rw [hInitialTotal] at hBound
  simpa [
    K,
    embedding,
    initial,
    physicalVariation,
    rowCoefficient,
    auxCoefficient,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate] using
    hBound

end

end MathlibAnalytic
end MGAP4D
