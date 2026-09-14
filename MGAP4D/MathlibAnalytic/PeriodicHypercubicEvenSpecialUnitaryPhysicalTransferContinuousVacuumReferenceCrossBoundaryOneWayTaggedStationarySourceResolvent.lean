import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryOneWayTaggedStationaryNonstrictBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance referenceCrossBoundaryOneWayTaggedStationarySourceResolventSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- In the C5 tagged carrier, the reciprocal random-scan normalization and its
resolvent cancel the tagged-index cardinality exactly.  This is a scaling
identity for the one-way carrier, not a volume-uniform one-coordinate rate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_invCard_mul_invOneSubReciprocalRate_eq_invOneSubCoefficient
    (H : ℕ)
    (beta : ℝ)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold) :
    (Fintype.card
        (Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ)⁻¹ *
        (1 -
          finiteInfluenceKernelReciprocalRandomScanRate
            (Sum
              (PeriodicHypercubicEvenSpatialSliceLink H)
              (PeriodicHypercubicEvenSpatialSliceLink H))
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
              beta))⁻¹ =
      (1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
          beta)⁻¹ := by
  exact
    inv_card_mul_inv_one_sub_reciprocalRate
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedIndex_card_pos
        H)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
        beta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient_lt_one_of_beta_lt
        beta hBetaLt)

/-- Source-summing singleton stationary responses removes the random-scan
cardinality loss and leaves the volume-independent C5 resolvent
`(1 - q(beta))⁻¹`.  Only the already-proved one-way tagged carrier enters. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_partialSource_singleton_sum_source_le_resolvent
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    (sourceEnvelope :
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ)
    (hEnvelopeNonneg : ∀ e, 0 ≤ sourceEnvelope e)
    (magnitude : ℝ)
    (hMagnitude : 0 ≤ magnitude)
    (n : ℕ) :
    (∑ source :
        Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H),
      finiteInfluenceKernelPartialSource
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
          H beta hbeta)
        sourceEnvelope
        (finiteInfluenceKernelSingletonVariation magnitude source)
        n) ≤
      finiteProductVariationTotal sourceEnvelope * magnitude *
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
            beta)⁻¹ := by
  exact le_rfl

end

end MathlibAnalytic
end MGAP4D
