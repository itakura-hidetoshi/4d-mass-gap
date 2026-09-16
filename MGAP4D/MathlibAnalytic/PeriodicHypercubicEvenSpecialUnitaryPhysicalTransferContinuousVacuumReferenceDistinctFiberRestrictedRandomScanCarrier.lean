import MGAP4D.MathlibAnalytic.FiniteInfluenceKernelRestrictedTargetRandomScan
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberDeterministicScheduleCarrierLemmas
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance referenceDistinctFiberRestrictedRandomScanCarrierSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- One uniform physical-target random-scan step on the explicit augmented C5
carrier.  Only actual physical fibers `Sum.inl fiber` are eligible targets;
represented boundary-source coordinates `Sum.inr source` are not scanned. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanUpdatedVariation
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (profile : Sum
      (PeriodicHypercubicEvenSpatialSliceLink H)
      (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ)
    (e : Sum
      (PeriodicHypercubicEvenSpatialSliceLink H)
      (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ :=
  finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
      H beta hbeta)
    (fun fiber : PeriodicHypercubicEvenSpatialSliceLink H => Sum.inl fiber)
    profile e

/-- The physical-target restricted scan is exactly the uniform average of the
already-proved singleton deterministic C5 carrier schedules. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanUpdatedVariation_leftVariation_eq_uniformAverage_singletonSchedule
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (e : Sum
      (PeriodicHypercubicEvenSpatialSliceLink H)
      (PeriodicHypercubicEvenSpatialSliceLink H)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanUpdatedVariation
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation
          H variation)
        e =
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        ∑ fiber : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation
            H beta hbeta variation [fiber] e := by
  rfl

/-- Iterated uniform physical-target random-scan profile on the explicit C5
tagged carrier.  This is deliberately a restricted-target iterate, not the
full random scan over `Sum Link Link`. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) :
    ℕ →
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ :=
  finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
      H beta hbeta)
    (fun fiber : PeriodicHypercubicEvenSpatialSliceLink H => Sum.inl fiber)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation
      H variation)

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate_zero
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
        H beta hbeta variation 0 =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation
        H variation := by
  rfl

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate_succ
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
        H beta hbeta variation (n + 1) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanUpdatedVariation
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
          H beta hbeta variation n) := by
  rfl

/-- The physical-target restricted iterate preserves nonnegativity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate_nonneg
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (n : ℕ)
    (e : Sum
      (PeriodicHypercubicEvenSpatialSliceLink H)
      (PeriodicHypercubicEvenSpatialSliceLink H)) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
        H beta hbeta variation n e := by
  have hInitial :
      ∀ x : Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H),
        0 ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation
            H variation x := by
    intro x
    cases x with
    | inl x =>
        simpa [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation] using
          hVariationNonneg x
    | inr x =>
        simp [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation]
  exact
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
        H beta hbeta)
      (fun fiber : PeriodicHypercubicEvenSpatialSliceLink H => Sum.inl fiber)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation
        H variation)
      hInitial n e

end

end MathlibAnalytic
end MGAP4D
