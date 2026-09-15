import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelResponseCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance referenceCrossBoundaryOneWayTaggedKernelResponseCertificateConstructorSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Package a continuous-state comparison into the state-space-independent C5
kernel-response interface once its discrepancy, common source bound, and
finite-step kernel residual inequality have been proved.

This constructor adds no finite-state realization and no reverse-influence
claim.  It only packages the witnesses required by
`FiniteKernelStationaryResponseFamilyCertificate`. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_kernelResponseCertificateOfResidual
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (magnitude : ℝ)
    (hMagnitude : 0 ≤ magnitude)
    (discrepancy :
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ)
    (sourceBound :
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ)
    (hSourceBoundNonneg : ∀ e, 0 ≤ sourceBound e)
    (hKernelResidual :
      ∀ source :
          Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H),
        ∀ sourceEnvelope :
          Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ,
          (∀ e, 0 ≤ sourceEnvelope e) →
          (∀ e, sourceBound e ≤ sourceEnvelope e) →
          ∀ n : ℕ,
            discrepancy source ≤
              finiteInfluenceKernelPartialSource
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
                    H beta hbeta)
                  sourceEnvelope
                  (finiteInfluenceKernelSingletonVariation magnitude source) n +
                2 * finiteProductVariationTotal
                  (finiteInfluenceKernelRandomScanVariationIterate
                    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
                      H beta hbeta)
                    (finiteInfluenceKernelSingletonVariation magnitude source) n)) :
    FiniteKernelStationaryResponseFamilyCertificate
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
        H beta hbeta)
      (fun source :
          Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H) =>
        finiteInfluenceKernelSingletonVariation magnitude source) := by
  classical
  refine
    { discrepancy := discrepancy
      sourceBound := sourceBound
      sourceBound_nonneg := hSourceBoundNonneg
      variation_nonneg := ?_
      discrepancy_le_kernelResidual := hKernelResidual }
  intro source e
  by_cases h : e = source
  · subst e
    simp [finiteInfluenceKernelSingletonVariation, hMagnitude]
  · simp [finiteInfluenceKernelSingletonVariation, h]

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_kernelResponseCertificateOfResidual_discrepancy
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (magnitude : ℝ)
    (hMagnitude : 0 ≤ magnitude)
    (discrepancy sourceBound :
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ)
    (hSourceBoundNonneg : ∀ e, 0 ≤ sourceBound e)
    (hKernelResidual) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_kernelResponseCertificateOfResidual
      H beta hbeta magnitude hMagnitude discrepancy sourceBound
      hSourceBoundNonneg hKernelResidual).discrepancy = discrepancy := by
  rfl

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_kernelResponseCertificateOfResidual_sourceBound
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (magnitude : ℝ)
    (hMagnitude : 0 ≤ magnitude)
    (discrepancy sourceBound :
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ)
    (hSourceBoundNonneg : ∀ e, 0 ≤ sourceBound e)
    (hKernelResidual) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_kernelResponseCertificateOfResidual
      H beta hbeta magnitude hMagnitude discrepancy sourceBound
      hSourceBoundNonneg hKernelResidual).sourceBound = sourceBound := by
  rfl

/-- Direct continuous-comparison entry point for the C5 source-summed
resolvent estimate.  A caller supplies the actually proved discrepancy,
source bound, and kernel-residual inequality; the certificate is built and
consumed internally. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_discrepancy_singleton_sum_source_le_resolvent_add_geometricResidual_of_kernelResidual
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    (magnitude : ℝ)
    (hMagnitude : 0 ≤ magnitude)
    (discrepancy :
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ)
    (sourceBound :
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ)
    (hSourceBoundNonneg : ∀ e, 0 ≤ sourceBound e)
    (hKernelResidual :
      ∀ source :
          Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H),
        ∀ sourceEnvelope :
          Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ,
          (∀ e, 0 ≤ sourceEnvelope e) →
          (∀ e, sourceBound e ≤ sourceEnvelope e) →
          ∀ n : ℕ,
            discrepancy source ≤
              finiteInfluenceKernelPartialSource
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
                    H beta hbeta)
                  sourceEnvelope
                  (finiteInfluenceKernelSingletonVariation magnitude source) n +
                2 * finiteProductVariationTotal
                  (finiteInfluenceKernelRandomScanVariationIterate
                    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
                      H beta hbeta)
                    (finiteInfluenceKernelSingletonVariation magnitude source) n))
    (sourceEnvelope :
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ)
    (hEnvelopeNonneg : ∀ e, 0 ≤ sourceEnvelope e)
    (hEnvelope : ∀ e, sourceBound e ≤ sourceEnvelope e)
    (n : ℕ) :
    (∑ source :
        Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H),
      discrepancy source) ≤
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
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_kernelResponseCertificate_discrepancy_singleton_sum_source_le_resolvent_add_geometricResidual
      H beta hbeta hBetaLt magnitude hMagnitude
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_kernelResponseCertificateOfResidual
        H beta hbeta magnitude hMagnitude discrepancy sourceBound
        hSourceBoundNonneg hKernelResidual)
      sourceEnvelope hEnvelopeNonneg hEnvelope n

end

end MathlibAnalytic
end MGAP4D
