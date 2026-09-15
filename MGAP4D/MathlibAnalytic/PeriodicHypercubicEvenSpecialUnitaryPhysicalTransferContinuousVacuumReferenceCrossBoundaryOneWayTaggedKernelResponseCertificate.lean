import MGAP4D.MathlibAnalytic.FiniteKernelStationaryResponseCertificate
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryOneWayTaggedStationarySourceResolvent
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance referenceCrossBoundaryOneWayTaggedKernelResponseCertificateSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The source-summed C5 resolvent estimate depends only on a
state-space-independent kernel-response certificate.  In particular, the
local state space need not be finite at this interface.

A continuous SU(N) comparison may therefore enter here once it supplies this
certificate for the proved one-way tagged carrier.  This theorem does not
assert such a construction, does not identify the carrier with an
unrepresented reverse physical influence, and does not assert physical
Poincare/coercivity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_kernelResponseCertificate_discrepancy_singleton_sum_source_le_resolvent_add_geometricResidual
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    (magnitude : ℝ)
    (hMagnitude : 0 ≤ magnitude)
    (C : FiniteKernelStationaryResponseFamilyCertificate
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
        H beta hbeta)
      (fun source :
          Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H) =>
        finiteInfluenceKernelSingletonVariation magnitude source))
    (sourceEnvelope :
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ)
    (hEnvelopeNonneg : ∀ e, 0 ≤ sourceEnvelope e)
    (hEnvelope : ∀ e, C.sourceBound e ≤ sourceEnvelope e)
    (n : ℕ) :
    (∑ source :
        Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H),
      C.discrepancy source) ≤
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
  have hEach :
      ∀ source :
          Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H),
        C.discrepancy source ≤
          finiteInfluenceKernelPartialSource
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
                H beta hbeta)
              sourceEnvelope
              (finiteInfluenceKernelSingletonVariation magnitude source) n +
            2 * finiteProductVariationTotal
              (finiteInfluenceKernelRandomScanVariationIterate
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
                  H beta hbeta)
                (finiteInfluenceKernelSingletonVariation magnitude source) n) := by
    intro source
    exact C.discrepancy_le_kernelResidual
      source sourceEnvelope hEnvelopeNonneg hEnvelope n
  have hSummed :
      (∑ source :
          Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H),
        C.discrepancy source) ≤
        ∑ source :
          Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H),
          (finiteInfluenceKernelPartialSource
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
                H beta hbeta)
              sourceEnvelope
              (finiteInfluenceKernelSingletonVariation magnitude source) n +
            2 * finiteProductVariationTotal
              (finiteInfluenceKernelRandomScanVariationIterate
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
                  H beta hbeta)
                (finiteInfluenceKernelSingletonVariation magnitude source) n)) := by
    apply Finset.sum_le_sum
    intro source _hsource
    exact hEach source
  have hSource :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_partialSource_singleton_sum_source_le_resolvent
      H beta hbeta hBetaLt sourceEnvelope hEnvelopeNonneg
      magnitude hMagnitude n
  have hTerminal :=
    finiteInfluenceKernelSingletonVariation_iterate_total_sum_source_le
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
        H beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedIndex_card_pos
        H)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
        beta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient_nonneg
        beta hbeta)
      (fun source =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData_columnSum_le_coefficient
          H beta hbeta source)
      magnitude hMagnitude n
  have hTerminalScaled :
      (∑ source :
          Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H),
        2 * finiteProductVariationTotal
          (finiteInfluenceKernelRandomScanVariationIterate
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
              H beta hbeta)
            (finiteInfluenceKernelSingletonVariation magnitude source) n)) ≤
        2 *
          ((Fintype.card
            (Sum
              (PeriodicHypercubicEvenSpatialSliceLink H)
              (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ) *
            (finiteInfluenceKernelReciprocalRandomScanRate
                (Sum
                  (PeriodicHypercubicEvenSpatialSliceLink H)
                  (PeriodicHypercubicEvenSpatialSliceLink H))
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
                  beta) ^ n * magnitude)) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hTerminal (by norm_num)
  calc
    (∑ source :
        Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H),
      C.discrepancy source) ≤
        ∑ source :
          Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H),
          (finiteInfluenceKernelPartialSource
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
                H beta hbeta)
              sourceEnvelope
              (finiteInfluenceKernelSingletonVariation magnitude source) n +
            2 * finiteProductVariationTotal
              (finiteInfluenceKernelRandomScanVariationIterate
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
                  H beta hbeta)
                (finiteInfluenceKernelSingletonVariation magnitude source) n)) := hSummed
    _ =
        (∑ source :
            Sum
              (PeriodicHypercubicEvenSpatialSliceLink H)
              (PeriodicHypercubicEvenSpatialSliceLink H),
          finiteInfluenceKernelPartialSource
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
              H beta hbeta)
            sourceEnvelope
            (finiteInfluenceKernelSingletonVariation magnitude source) n) +
          (∑ source :
            Sum
              (PeriodicHypercubicEvenSpatialSliceLink H)
              (PeriodicHypercubicEvenSpatialSliceLink H),
            2 * finiteProductVariationTotal
              (finiteInfluenceKernelRandomScanVariationIterate
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
                  H beta hbeta)
                (finiteInfluenceKernelSingletonVariation magnitude source) n)) := by
          rw [Finset.sum_add_distrib]
    _ ≤
        finiteProductVariationTotal sourceEnvelope * magnitude *
            (1 -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
                beta)⁻¹ +
          2 *
            ((Fintype.card
              (Sum
                (PeriodicHypercubicEvenSpatialSliceLink H)
                (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ) *
              (finiteInfluenceKernelReciprocalRandomScanRate
                  (Sum
                    (PeriodicHypercubicEvenSpatialSliceLink H)
                    (PeriodicHypercubicEvenSpatialSliceLink H))
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
                    beta) ^ n * magnitude)) :=
        add_le_add hSource hTerminalScaled
    _ =
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
                  beta) ^ n * magnitude) := by ring

end

end MathlibAnalytic
end MGAP4D
