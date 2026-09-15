import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberDeterministicScheduleCarrier
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance referenceDistinctFiberDeterministicScheduleCarrierLemmasSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel_left_right
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
        H beta hbeta).influence (Sum.inl target) (Sum.inr source) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
        beta target source := by
  rfl

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel_left_left_of_ne
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistinct : target ≠ source) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
        H beta hbeta).influence (Sum.inl target) (Sum.inl source) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
        beta := by
  let offFiberInfluence :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    fun _target _source =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
        beta
  have hOffFiberInfluenceNonneg :
      ∀ a b, 0 ≤ offFiberInfluence a b := by
    intro a b
    dsimp [offFiberInfluence]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence_nonneg
        beta hbeta
  have hLeft :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedKernelData_left_left
      H beta hbeta offFiberInfluence hOffFiberInfluenceNonneg target source hDistinct
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel,
    offFiberInfluence] using hLeft

/-- Every explicit tagged deterministic schedule profile is nonnegative when the
initial physical variation profile is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation_nonneg
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (fibers : List (PeriodicHypercubicEvenSpatialSliceLink H))
    (e : Sum
      (PeriodicHypercubicEvenSpatialSliceLink H)
      (PeriodicHypercubicEvenSpatialSliceLink H)) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation
        H beta hbeta variation fibers e := by
  apply
    finiteInfluenceKernelDeterministicScheduleVariation_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
        H beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation
        H variation)
  · intro x
    cases x with
    | inl x =>
        simpa [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation] using
          hVariationNonneg x
    | inr x =>
        simp [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation]
  · exact fibers.map Sum.inl
  · exact e

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation_cons_right
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (fiber source : PeriodicHypercubicEvenSpatialSliceLink H)
    (fibers : List (PeriodicHypercubicEvenSpatialSliceLink H)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation
        H beta hbeta variation (fiber :: fibers) (Sum.inr source) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation
          H beta hbeta variation fibers (Sum.inr source) +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
            beta fiber source *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation
            H beta hbeta variation fibers (Sum.inl fiber) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation_cons]
  simp [finiteInfluenceKernelUpdatedVariation]

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation_cons_left_same
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (fibers : List (PeriodicHypercubicEvenSpatialSliceLink H)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation
        H beta hbeta variation (fiber :: fibers) (Sum.inl fiber) = 0 := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation_cons]
  simp [finiteInfluenceKernelUpdatedVariation]

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation_cons_left_of_ne
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (fiber background : PeriodicHypercubicEvenSpatialSliceLink H)
    (fibers : List (PeriodicHypercubicEvenSpatialSliceLink H))
    (hDistinct : background ≠ fiber) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation
        H beta hbeta variation (fiber :: fibers) (Sum.inl background) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation
          H beta hbeta variation fibers (Sum.inl background) +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
            beta *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation
            H beta hbeta variation fibers (Sum.inl fiber) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation_cons]
  unfold finiteInfluenceKernelUpdatedVariation
  simp only [Sum.inl.injEq, hDistinct, if_false]
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel_left_left_of_ne
      H beta hbeta fiber background (Ne.symm hDistinct)]

end

end MathlibAnalytic
end MGAP4D
