import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryInfluenceOperator
import MGAP4D.MathlibAnalytic.FinitePositiveWeightReciprocalInfluenceKernelResponse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance referenceCrossBoundaryOneWayTaggedCarrierSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- One-way tagged C5 cross-boundary influence. `Sum.inl` is the left target
copy and `Sum.inr` is the right source copy. Only the already-proved
right-source to left-target block is represented. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedInfluence
    (H : ℕ)
    (beta : ℝ) :
    Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) →
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ
  | Sum.inl fiber, Sum.inr source =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
        beta fiber source
  | _, _ => 0

/-- RED theorem: nonnegativity is not definitionally reducible in the populated
left-target/right-source block. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedInfluence_nonneg
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source :
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H)) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedInfluence
        H beta target source := by
  rfl

end

end MathlibAnalytic
end MGAP4D
