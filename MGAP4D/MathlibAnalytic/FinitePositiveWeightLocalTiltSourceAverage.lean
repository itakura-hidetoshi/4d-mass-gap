import MGAP4D.MathlibAnalytic.FinitePositiveWeightNonstrictStationaryResponse
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryOneWayTaggedStationaryUniformAverageSource
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance finitePositiveWeightLocalTiltSourceAverageSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The explicit source vector of a bounded local multiplicative tilt has
volume-normalized total bounded by the same likelihood-ratio constant.  This
is the generic source-average certificate needed by the stationary C5 bridge. -/
theorem finitePositiveWeightLocalTiltConditionalSourceBound_total_le_card_mul
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (support : Finset ι)
    (lower upper : ℝ)
    (hLower : 0 < lower)
    (hUpper : 0 < upper)
    (hLowerUpper : lower ≤ upper) :
    finiteProductVariationTotal
        (finitePositiveWeightLocalTiltConditionalSourceBound
          support lower upper) ≤
      (Fintype.card ι : ℝ) *
        (2 * (1 - (upper / lower)⁻¹)) := by
  have hRatioOne : 1 ≤ upper / lower :=
    (le_div_iff₀ hLower).2 (by simpa using hLowerUpper)
  have hRatioPos : 0 < upper / lower := div_pos hUpper hLower
  have hInvLeOne : (upper / lower)⁻¹ ≤ 1 :=
    (inv_le_one₀ hRatioPos).2 hRatioOne
  have hConstNonneg :
      0 ≤ 2 * (1 - (upper / lower)⁻¹) := by
    nlinarith
  unfold finiteProductVariationTotal
  calc
    (∑ target : ι,
      finitePositiveWeightLocalTiltConditionalSourceBound
        support lower upper target) ≤
      ∑ _target : ι, (2 * (1 - (upper / lower)⁻¹)) := by
        apply Finset.sum_le_sum
        intro target _htarget
        unfold finitePositiveWeightLocalTiltConditionalSourceBound
        split
        · exact le_rfl
        · exact hConstNonneg
    _ = (Fintype.card ι : ℝ) *
        (2 * (1 - (upper / lower)⁻¹)) := by
      simp

/-- A bounded finite-support multiplicative tilt can be inserted directly into
the C5 stationary uniform-average source theorem.  The result remains a
finite positive-weight comparison theorem; it does not identify the finite
comparison model with the full four-dimensional Wilson conditional law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_localTiltAverageExpectationDiscrepancy_singleton_le_uniformAverageSourceResolvent_add_expSweepResidual
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    {G : Type}
    [Fintype G]
    [Nonempty G]
    (weight tilt :
      (Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H) → G) → ℝ)
    (hweight : ∀ A, 0 < weight A)
    (htilt : ∀ A, 0 < tilt A)
    (support :
      Finset
        (Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H)))
    (htiltSupport : FiniteProductFunctionSupportedOn support tilt)
    (lower upper : ℝ)
    (hLower : 0 < lower)
    (hUpper : 0 < upper)
    (hLowerUpper : lower ≤ upper)
    (htiltLower : ∀ A, lower ≤ tilt A)
    (htiltUpper : ∀ A, tilt A ≤ upper)
    (D : FinitePositiveWeightNonstrictL1MatrixData weight)
    (hDomination :
      FinitePositiveWeightNonstrictInfluenceDominatedBy
        D
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
          H beta hbeta).influence)
    (f :
      Sum
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H) →
        ((Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H) → G) → ℝ))
    (P : ∀ source,
      FiniteProductVariationBound (f source))
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
        |finitePositiveWeightGlobalExpectation
            (finitePositiveWeightMultiplicativeTilt weight tilt)
            (f source) -
          finitePositiveWeightGlobalExpectation weight (f source)|) ≤
      (2 * (1 - (upper / lower)⁻¹)) *
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
  have hCard :
      0 <
        Fintype.card
          (Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H)) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedIndex_card_pos
      H
  let comparison :=
    finitePositiveWeightLocalTiltStationaryNonstrictComparisonData
      weight tilt hweight htilt support htiltSupport
      lower upper hLower hUpper hLowerUpper htiltLower htiltUpper
      hCard D
  have hRatioOne : 1 ≤ upper / lower :=
    (le_div_iff₀ hLower).2 (by simpa using hLowerUpper)
  have hRatioPos : 0 < upper / lower := div_pos hUpper hLower
  have hInvLeOne : (upper / lower)⁻¹ ≤ 1 :=
    (inv_le_one₀ hRatioPos).2 hRatioOne
  have hSourceAverageNonneg :
      0 ≤ 2 * (1 - (upper / lower)⁻¹) := by
    nlinarith
  have hComparisonDomination :
      FinitePositiveWeightNonstrictInfluenceDominatedBy
        comparison.rightInfluence
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
          H beta hbeta).influence := by
    change
      FinitePositiveWeightNonstrictInfluenceDominatedBy
        D
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedKernelData
          H beta hbeta).influence
    exact hDomination
  have hSourceAverage :
      finiteProductVariationTotal comparison.sourceBound ≤
        (Fintype.card
          (Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ) *
          (2 * (1 - (upper / lower)⁻¹)) := by
    change
      finiteProductVariationTotal
          (finitePositiveWeightLocalTiltConditionalSourceBound
            support lower upper) ≤
        (Fintype.card
          (Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ) *
          (2 * (1 - (upper / lower)⁻¹))
    exact
      finitePositiveWeightLocalTiltConditionalSourceBound_total_le_card_mul
        support lower upper hLower hUpper hLowerUpper
  have hBound :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_averageExpectationDiscrepancy_singleton_le_uniformAverageSourceResolvent_add_expSweepResidual
      H beta hbeta hBetaLt f P comparison hComparisonDomination
      comparison.sourceBound comparison.sourceBound_nonneg
      (fun _ => le_rfl)
      (2 * (1 - (upper / lower)⁻¹)) hSourceAverageNonneg hSourceAverage
      magnitude hMagnitude hSingleton sweeps
  simpa only [
    FinitePositiveWeightStationaryNonstrictComparisonData.expectationDiscrepancy] using hBound

end

end MathlibAnalytic
end MGAP4D
