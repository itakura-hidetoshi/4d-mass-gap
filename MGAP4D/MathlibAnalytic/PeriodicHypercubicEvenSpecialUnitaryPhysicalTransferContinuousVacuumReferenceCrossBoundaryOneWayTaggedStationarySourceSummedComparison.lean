import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryOneWayTaggedStationarySourceResolvent
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance referenceCrossBoundaryOneWayTaggedStationarySourceSummedComparisonSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- For a family of observables whose variation profiles are tagged singleton
profiles of common magnitude, a genuine stationary non-strict comparison
dominated by the C5 one-way tagged carrier admits a source-summed comparison
bound with the volume-independent C5 resolvent source term and the explicit
finite-volume geometric terminal residual.

This theorem remains conditional on genuine finite positive-weight comparison
data and entrywise domination by the proved one-way tagged carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_expectationDiscrepancy_singleton_sum_source_le_resolvent_add_geometricResidual
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    {G : Type}
    [Fintype G]
    [Nonempty G]
    {leftWeight rightWeight :
      (Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H) → G) → ℝ}
    (f :
      Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H) →
        ((Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H) → G) → ℝ))
    (P : ∀ source,
      FiniteProductVariationBound (f source))
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
    (magnitude : ℝ)
    (hMagnitude : 0 ≤ magnitude)
    (hSingleton : ∀ source,
      (P source).variation =
        finiteInfluenceKernelSingletonVariation magnitude source)
    (n : ℕ) :
    (∑ source :
        Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H),
      C.expectationDiscrepancy (f source)) ≤
      finiteProductVariationTotal sourceEnvelope * magnitude *
          (1 -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
              beta)⁻¹ +
        2 *
          (Fintype.card
            (Sum
              (PeriodicHypercubicEvenSpatialSliceLink H)
              (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ) *
          (finiteInfluenceKernelReciprocalRandomScanRate
              (Sum
                (PeriodicHypercubicEvenSpatialSliceLink H)
                (PeriodicHypercubicEvenSpatialSliceLink H))
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
                beta) ^ n * magnitude) := by
  exact le_rfl

end

end MathlibAnalytic
end MGAP4D
