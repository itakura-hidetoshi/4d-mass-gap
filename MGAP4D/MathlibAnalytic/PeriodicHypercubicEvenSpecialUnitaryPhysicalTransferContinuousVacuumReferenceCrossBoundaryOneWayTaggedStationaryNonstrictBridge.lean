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
  have hPartial :=
    C.partialStationarySource_le_kernel
      P
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
        H beta hbeta)
      hDomination sourceEnvelope hEnvelopeNonneg hEnvelope n
  have hTerminal :
      finiteProductVariationTotal
          (C.rightRandomScanIterateVariationBound P n).variation ≤
        finiteProductVariationTotal
          (finiteInfluenceKernelRandomScanVariationIterate
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
              H beta hbeta)
            P.variation n) := by
    unfold finiteProductVariationTotal
    apply Finset.sum_le_sum
    intro e _he
    rw [C.rightRandomScanIterateVariation_eq P n]
    exact
      finitePositiveWeightNonstrictRandomScanVariationIterate_le_kernel
        C.rightInfluence
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
          H beta hbeta)
        hDomination P.variation P.variation_nonneg n e
  have hFinite :=
    C.expectationDiscrepancy_le_partialSource_add_two_mul_terminalVariation
      P n
  exact hFinite.trans
    (add_le_add hPartial
      (mul_le_mul_of_nonneg_left hTerminal (by norm_num)))

/-- The same interface has an explicit finite-volume geometric terminal
residual.  Its rate is exactly the reciprocal random-scan rate already proved
strictly below one in the C5 small-coupling regime.  The explicit tagged-card
factor is retained; no volume-uniform one-coordinate rate is claimed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_expectationDiscrepancy_le_partialSource_add_geometricResidual
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
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound : ∀ e, P.variation e ≤ bound)
    (n : ℕ) :
    C.expectationDiscrepancy f ≤
      finiteInfluenceKernelPartialSource
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
            H beta hbeta)
          sourceEnvelope P.variation n +
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
                beta) ^ n * bound) := by
  have hBase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_expectationDiscrepancy_le_kernelResidual
      H beta hbeta P C hDomination sourceEnvelope
      hEnvelopeNonneg hEnvelope n
  have hTerminal :
      finiteProductVariationTotal
          (finiteInfluenceKernelRandomScanVariationIterate
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
              H beta hbeta)
            P.variation n) ≤
        (Fintype.card
          (Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ) *
          (finiteInfluenceKernelReciprocalRandomScanRate
              (Sum
                (PeriodicHypercubicEvenSpatialSliceLink H)
                (PeriodicHypercubicEvenSpatialSliceLink H))
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
                beta) ^ n * bound) := by
    unfold finiteProductVariationTotal
    calc
      (∑ source :
          Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H),
          finiteInfluenceKernelRandomScanVariationIterate
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
              H beta hbeta)
            P.variation n source) ≤
        ∑ _source :
          Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H),
          (finiteInfluenceKernelReciprocalRandomScanRate
              (Sum
                (PeriodicHypercubicEvenSpatialSliceLink H)
                (PeriodicHypercubicEvenSpatialSliceLink H))
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
                beta) ^ n * bound) := by
          apply Finset.sum_le_sum
          intro source _hsource
          exact
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_randomScanVariationIterate_le_rate_pow_mul
              H beta hbeta P.variation P.variation_nonneg
              bound hBoundNonneg hVariationBound n source
      _ =
        (Fintype.card
          (Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ) *
          (finiteInfluenceKernelReciprocalRandomScanRate
              (Sum
                (PeriodicHypercubicEvenSpatialSliceLink H)
                (PeriodicHypercubicEvenSpatialSliceLink H))
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
                beta) ^ n * bound) := by
          simp [nsmul_eq_mul]
  have hTerminalScaled :
      2 * finiteProductVariationTotal
          (finiteInfluenceKernelRandomScanVariationIterate
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
              H beta hbeta)
            P.variation n) ≤
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
                beta) ^ n * bound) := by
    calc
      2 * finiteProductVariationTotal
          (finiteInfluenceKernelRandomScanVariationIterate
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
              H beta hbeta)
            P.variation n) ≤
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
                  beta) ^ n * bound)) :=
        mul_le_mul_of_nonneg_left hTerminal (by norm_num)
      _ =
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
                beta) ^ n * bound) := by ring
  exact hBase.trans
    (add_le_add (le_refl _) hTerminalScaled)

end

end MathlibAnalytic
end MGAP4D
