import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryOneWayTaggedStationarySweepAverage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance referenceCrossBoundaryOneWayTaggedStationaryUniformAverageSourceSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- If the genuine stationary source envelope has a uniform bound on its
normalized finite-product total, then the C5 stationary sweep comparison is
fully volume-independent at the interface level.

This is still a conditional finite positive-weight comparison theorem.  It
does not identify the C5 reference law with the full four-dimensional Wilson
conditional law, and it does not assert physical Poincare/coercivity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_averageExpectationDiscrepancy_singleton_le_uniformAverageSourceResolvent_add_expSweepResidual
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
    (sourceAverageBound : ℝ)
    (hSourceAverageNonneg : 0 ≤ sourceAverageBound)
    (hSourceAverage :
      finiteProductVariationTotal sourceEnvelope ≤
        (Fintype.card
          (Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ) *
          sourceAverageBound)
    (magnitude : ℝ)
    (hMagnitude : 0 ≤ magnitude)
    (hSingleton : ∀ source,
      (P source).variation =
        finiteInfluenceKernelSingletonVariation magnitude source)
    (sweeps : ℕ) :
    (Fintype.card
        (Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ)⁻¹ *
      (∑ source :
          Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H),
        C.expectationDiscrepancy (f source)) ≤
      sourceAverageBound *
          magnitude *
          (1 -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
              beta)⁻¹ +
        2 *
          (Real.exp
              (-(1 -
                  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
                    beta) * (sweeps : ℝ)) *
            magnitude) := by
  have hCardNat :
      0 <
        Fintype.card
          (Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H)) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedIndex_card_pos
      H
  have hCard :
      0 <
        (Fintype.card
          (Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ) := by
    exact_mod_cast hCardNat
  have hCardNe :
      (Fintype.card
        (Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ) ≠ 0 :=
    ne_of_gt hCard
  have hNormalizedSource :
      (Fintype.card
          (Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ)⁻¹ *
          finiteProductVariationTotal sourceEnvelope ≤
        sourceAverageBound := by
    calc
      (Fintype.card
          (Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ)⁻¹ *
          finiteProductVariationTotal sourceEnvelope ≤
        (Fintype.card
            (Sum
              (PeriodicHypercubicEvenSpatialSliceLink H)
              (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ)⁻¹ *
          ((Fintype.card
              (Sum
                (PeriodicHypercubicEvenSpatialSliceLink H)
                (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ) *
            sourceAverageBound) := by
              exact mul_le_mul_of_nonneg_left hSourceAverage
                (inv_nonneg.mpr hCard.le)
      _ = sourceAverageBound := by
        field_simp [hCardNe]
  have hqLtOne :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
          beta < 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient_lt_one_of_beta_lt
      beta hBetaLt
  have hGapInvNonneg :
      0 ≤
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
            beta)⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr hqLtOne.le)
  have hSourceTerm :
      ((Fintype.card
          (Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ)⁻¹ *
        finiteProductVariationTotal sourceEnvelope) *
          magnitude *
          (1 -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
              beta)⁻¹ ≤
        sourceAverageBound *
          magnitude *
          (1 -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
              beta)⁻¹ := by
    apply mul_le_mul_of_nonneg_right _ hGapInvNonneg
    exact mul_le_mul_of_nonneg_right hNormalizedSource hMagnitude
  have hBase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_averageExpectationDiscrepancy_singleton_le_normalizedResolvent_add_expSweepResidual
      H beta hbeta hBetaLt f P C hDomination sourceEnvelope
      hEnvelopeNonneg hEnvelope magnitude hMagnitude hSingleton sweeps
  exact hBase.trans (add_le_add_left hSourceTerm _)

end

end MathlibAnalytic
end MGAP4D
