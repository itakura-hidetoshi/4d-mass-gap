import MGAP4D.MathlibAnalytic.FiniteInfluenceKernelDeterministicSchedule
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDistinctFiberTwoStepTransport
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance referenceDistinctFiberDeterministicScheduleCarrierSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The fully explicit continuous-C5 augmented tagged carrier: the left-left
block is the normalized literal-C5 off-fiber coefficient and the left-right
block is the already-proved cross-boundary bounded-test majorant. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    FiniteNonnegativeInfluenceKernelData
      (Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H)) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTaggedKernelData
    H beta hbeta
    (fun _target _source =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
        beta)
    (by
      intro target source
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence_nonneg
          beta hbeta)

/-- Ordered deterministic target schedule on the explicit augmented tagged
carrier.  The physical left fibers are embedded with `Sum.inl`; the represented
boundary sources remain `Sum.inr`. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (fibers : List (PeriodicHypercubicEvenSpatialSliceLink H))
    (e : Sum
      (PeriodicHypercubicEvenSpatialSliceLink H)
      (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ :=
  finiteInfluenceKernelDeterministicScheduleVariation
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
      H beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation
      H variation)
    (fibers.map Sum.inl)
    e

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation_nil
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (e : Sum
      (PeriodicHypercubicEvenSpatialSliceLink H)
      (PeriodicHypercubicEvenSpatialSliceLink H)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation
        H beta hbeta variation [] e =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation
        H variation e := by
  rfl

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation_cons
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (fibers : List (PeriodicHypercubicEvenSpatialSliceLink H))
    (e : Sum
      (PeriodicHypercubicEvenSpatialSliceLink H)
      (PeriodicHypercubicEvenSpatialSliceLink H)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation
        H beta hbeta variation (fiber :: fibers) e =
      finiteInfluenceKernelUpdatedVariation
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
          H beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation
          H beta hbeta variation fibers)
        (Sum.inl fiber)
        e := by
  rfl

/-- Exact schedule-kernel representation of the explicit tagged deterministic
profile. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation_eq_sum_scheduleInfluenceKernel
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (fibers : List (PeriodicHypercubicEvenSpatialSliceLink H))
    (e : Sum
      (PeriodicHypercubicEvenSpatialSliceLink H)
      (PeriodicHypercubicEvenSpatialSliceLink H)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation
        H beta hbeta variation fibers e =
      ∑ initial : Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H),
        finiteHeatBathScheduleInfluenceKernel
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
              H beta hbeta).influence
            (fibers.map Sum.inl) initial e *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation
            H variation initial := by
  exact
    finiteInfluenceKernelDeterministicScheduleVariation_eq_sum_scheduleInfluenceKernel
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel
        H beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedLeftVariation
        H variation)
      (fibers.map Sum.inl) e

/-- The new arbitrary-list carrier specializes at two distinct fibers to the
already-proved explicit physical two-step coefficient.  This fixes the schedule
orientation: `[fiber₁, fiber₂]` means the tail update at `fiber₂` acts first and
the head update at `fiber₁` acts outside it. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation_pair_rightSource_eq
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (fiber₁ fiber₂ source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistinct : fiber₁ ≠ fiber₂) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation
        H beta hbeta variation [fiber₁, fiber₂] (Sum.inr source) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta fiber₂ source * variation fiber₂ +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta fiber₁ source *
          (variation fiber₁ +
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
              beta * variation fiber₂) := by
  let offFiberInfluence :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    fun _target _source =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence
        beta
  have hOffFiberInfluenceNonneg :
      ∀ target source, 0 ≤ offFiberInfluence target source := by
    intro target source
    dsimp [offFiberInfluence]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberOffFiberInfluence_nonneg
        beta hbeta
  have hPair :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryDistinctFiberTagged_twoTargetUpdatedVariation_rightSource_eq
      H beta hbeta offFiberInfluence hOffFiberInfluenceNonneg variation
      fiber₁ fiber₂ source hDistinct
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedDeterministicScheduleVariation,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedKernel,
    finiteInfluenceKernelDeterministicScheduleVariation,
    offFiberInfluence] using hPair

end

end MathlibAnalytic
end MGAP4D
