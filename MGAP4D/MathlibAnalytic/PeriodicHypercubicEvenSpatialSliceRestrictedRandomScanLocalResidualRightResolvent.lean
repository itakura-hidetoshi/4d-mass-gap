import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSliceRestrictedRandomScanLocalResidualSweep
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance spatialSliceRestrictedRandomScanLocalResidualRightResolventFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Under a strict local-plus-residual bound on the physical left-left block,
the accumulated forcing into one represented right-source coordinate has a
volume-independent reciprocal resolvent bound.

The represented right coordinate itself is not scanned, so its initial value
is retained.  Every later contribution comes from the physical left profile.
The reciprocal scan normalization cancels exactly against the geometric
resolvent denominator, leaving the volume-independent factor
`(1 - (18 * eta + rho))⁻¹`.

This is an abstract carrier theorem; it does not identify the older dense
distinct-fiber carrier with a sparse physical influence kernel. -/
theorem
    periodicHypercubicEvenSpatialSlice_sumRestrictedTargetRandomScanVariationIterate_inr_le_initial_add_sourceCoefficient_mul_bound_mul_invGap_of_local_residual
    (H : ℕ)
    (K :
      FiniteNonnegativeInfluenceKernelData
        (Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H)))
    (residual :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (eta rho : ℝ)
    (hEtaNonneg : 0 ≤ eta)
    (hRhoNonneg : 0 ≤ rho)
    (hResidualNonneg : ∀ target source, 0 ≤ residual target source)
    (hPointwise : ∀ target source,
      K.influence (Sum.inl target) (Sum.inl source) ≤
        (if target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source then
          eta else 0) + residual target source)
    (hResidualColumn : ∀ source,
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        residual target source) ≤ rho)
    (hStrict : 18 * eta + rho < 1)
    (variation :
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ)
    (hVariationNonneg :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        0 ≤ variation (Sum.inl e))
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        variation (Sum.inl e) ≤ bound)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceCoefficient : ℝ)
    (hSourceSum :
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        K.influence (Sum.inl target) (Sum.inr source)) ≤ sourceCoefficient)
    (n : ℕ) :
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
        K
        (fun target : PeriodicHypercubicEvenSpatialSliceLink H => Sum.inl target)
        variation n (Sum.inr source) ≤
      variation (Sum.inr source) +
        sourceCoefficient * bound *
          (1 - (18 * eta + rho))⁻¹ := by
  let Link := PeriodicHypercubicEvenSpatialSliceLink H
  let columnCoefficient : ℝ := 18 * eta + rho
  let rate : ℝ :=
    finiteInfluenceKernelReciprocalRandomScanRate Link columnCoefficient
  have hCard : 0 < Fintype.card Link := by
    simpa [Link] using periodicHypercubicEvenSpatialSliceLink_card_pos H
  have hColumnNonneg : 0 ≤ columnCoefficient := by
    dsimp [columnCoefficient]
    exact add_nonneg (mul_nonneg (by norm_num) hEtaNonneg) hRhoNonneg
  have hColumnLtOne : columnCoefficient < 1 := by
    simpa [columnCoefficient] using hStrict
  have hColumnSum :
      ∀ e : Link,
        finiteInfluenceKernelColumnSum
            (finiteInfluenceKernelSumLeftRestriction K) e ≤
          columnCoefficient := by
    intro e
    simpa [Link, columnCoefficient] using
      periodicHypercubicEvenSpatialSlice_sumLeftRestriction_columnSum_le_eighteen_mul_add_residualBound
        H K residual eta rho hEtaNonneg hResidualNonneg hPointwise
        hResidualColumn e
  have hRateNonneg : 0 ≤ rate := by
    dsimp [rate]
    exact
      finiteInfluenceKernelReciprocalRandomScanRate_nonneg
        hCard columnCoefficient hColumnNonneg
  have hRateLtOne : rate < 1 := by
    dsimp [rate]
    exact
      finiteInfluenceKernelReciprocalRandomScanRate_lt_one
        hCard columnCoefficient hColumnLtOne
  have hFinite :=
    finiteInfluenceKernelSumRestrictedTargetRandomScanVariationIterate_inr_le_geometricResidual
      K hCard columnCoefficient hColumnNonneg hColumnSum
      variation hVariationNonneg bound hBoundNonneg hVariationBound
      source sourceCoefficient hSourceSum n
  have hGeom :
      Finset.sum (Finset.range n) (fun j => rate ^ j) ≤
        (1 - rate)⁻¹ := by
    simpa [finiteRealGeometricSeries] using
      finiteRealGeometricSeries_le_inv_one_sub
        rate hRateNonneg hRateLtOne n
  have hSourceCoefficientNonneg : 0 ≤ sourceCoefficient := by
    have hSumNonneg :
        0 ≤
          ∑ target : Link,
            K.influence (Sum.inl target) (Sum.inr source) := by
      exact Finset.sum_nonneg fun target _ =>
        K.influence_nonneg (Sum.inl target) (Sum.inr source)
    have hSourceSum' :
        (∑ target : Link,
          K.influence (Sum.inl target) (Sum.inr source)) ≤
            sourceCoefficient := by
      simpa [Link] using hSourceSum
    exact hSumNonneg.trans hSourceSum'
  have hFactorNonneg :
      0 ≤
        (Fintype.card Link : ℝ)⁻¹ *
          sourceCoefficient * bound := by
    exact
      mul_nonneg
        (mul_nonneg
          (inv_nonneg.mpr (Nat.cast_nonneg _))
          hSourceCoefficientNonneg)
        hBoundNonneg
  have hCancel :
      (Fintype.card Link : ℝ)⁻¹ * (1 - rate)⁻¹ =
        (1 - columnCoefficient)⁻¹ := by
    dsimp [rate]
    exact
      inv_card_mul_inv_one_sub_reciprocalRate
        hCard columnCoefficient hColumnLtOne
  calc
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
        K
        (fun target : PeriodicHypercubicEvenSpatialSliceLink H => Sum.inl target)
        variation n (Sum.inr source) ≤
      variation (Sum.inr source) +
        (Fintype.card Link : ℝ)⁻¹ *
          sourceCoefficient * bound *
            Finset.sum (Finset.range n) (fun j => rate ^ j) := by
      simpa [Link, rate] using hFinite
    _ ≤
      variation (Sum.inr source) +
        (Fintype.card Link : ℝ)⁻¹ *
          sourceCoefficient * bound *
            (1 - rate)⁻¹ := by
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left hGeom hFactorNonneg)
        (variation (Sum.inr source))
    _ =
      variation (Sum.inr source) +
        ((Fintype.card Link : ℝ)⁻¹ * (1 - rate)⁻¹) *
          sourceCoefficient * bound := by
      ring
    _ =
      variation (Sum.inr source) +
        (1 - columnCoefficient)⁻¹ * sourceCoefficient * bound := by
      rw [hCancel]
    _ =
      variation (Sum.inr source) +
        sourceCoefficient * bound *
          (1 - (18 * eta + rho))⁻¹ := by
      dsimp [columnCoefficient]
      ring

/-- Specialization to a genuine physical-left variation profile.  Its tagged
lift has zero represented-right initial mass, so the previous theorem reduces
to a pure volume-independent accumulated-forcing bound. -/
theorem
    periodicHypercubicEvenSpatialSlice_taggedLeftVariation_sumRestrictedTargetRandomScanVariationIterate_inr_le_sourceCoefficient_mul_bound_mul_invGap_of_local_residual
    (H : ℕ)
    (K :
      FiniteNonnegativeInfluenceKernelData
        (Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H)))
    (residual :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (eta rho : ℝ)
    (hEtaNonneg : 0 ≤ eta)
    (hRhoNonneg : 0 ≤ rho)
    (hResidualNonneg : ∀ target source, 0 ≤ residual target source)
    (hPointwise : ∀ target source,
      K.influence (Sum.inl target) (Sum.inl source) ≤
        (if target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source then
          eta else 0) + residual target source)
    (hResidualColumn : ∀ source,
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        residual target source) ≤ rho)
    (hStrict : 18 * eta + rho < 1)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound : ∀ e, variation e ≤ bound)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceCoefficient : ℝ)
    (hSourceSum :
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        K.influence (Sum.inl target) (Sum.inr source)) ≤ sourceCoefficient)
    (n : ℕ) :
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
        K
        (fun target : PeriodicHypercubicEvenSpatialSliceLink H => Sum.inl target)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation
          H variation)
        n (Sum.inr source) ≤
      sourceCoefficient * bound *
        (1 - (18 * eta + rho))⁻¹ := by
  have hRaw :=
    periodicHypercubicEvenSpatialSlice_sumRestrictedTargetRandomScanVariationIterate_inr_le_initial_add_sourceCoefficient_mul_bound_mul_invGap_of_local_residual
      H K residual eta rho hEtaNonneg hRhoNonneg hResidualNonneg
      hPointwise hResidualColumn hStrict
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation
        H variation)
      (by
        intro e
        simpa [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation] using
          hVariationNonneg e)
      bound hBoundNonneg
      (by
        intro e
        simpa [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation] using
          hVariationBound e)
      source sourceCoefficient hSourceSum n
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation] using
    hRaw

end

end MathlibAnalytic
end MGAP4D
