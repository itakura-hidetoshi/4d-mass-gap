import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryOneWayTaggedColumnContraction
import MGAP4D.MathlibAnalytic.FinitePositiveWeightReciprocalInfluenceKernelResponse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance referenceCrossBoundaryOneWayTaggedStationarySpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Any genuine finite positive-weight stationary non-strict comparison whose
right influence is entrywise dominated by the one-way tagged C5 carrier has
its expectation discrepancy bounded by the corresponding C5 kernel response.

This is deliberately an interface theorem.  It does not identify the C5
continuous one-slab law with a finite product weight, and it does not assert
that an unrepresented reverse physical influence vanishes. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_expectationDiscrepancy_le_kernelResidual
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    {G : Type}
    [Fintype G]
    [Nonempty G]
    {leftWeight rightWeight :
      (Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H) → G) → ℝ}
    {f :
      (Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H) → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryNonstrictComparisonData
      leftWeight rightWeight)
    (hDomination :
      FinitePositiveWeightNonstrictInfluenceDominatedBy
        C.rightInfluence
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
          H beta hbeta).influence)
    (sourceEnvelope :
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ)
    (hEnvelopeNonneg : ∀ e, 0 ≤ sourceEnvelope e)
    (hEnvelope : ∀ e, C.sourceBound e ≤ sourceEnvelope e)
    (n : ℕ) :
    C.expectationDiscrepancy f ≤
      finiteInfluenceKernelPartialSource
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
            H beta hbeta)
          sourceEnvelope P.variation n +
        2 * finiteProductVariationTotal
          (finiteInfluenceKernelRandomScanVariationIterate
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
              H beta hbeta)
            P.variation n) := by
  exact le_rfl

end

end MathlibAnalytic
end MGAP4D
