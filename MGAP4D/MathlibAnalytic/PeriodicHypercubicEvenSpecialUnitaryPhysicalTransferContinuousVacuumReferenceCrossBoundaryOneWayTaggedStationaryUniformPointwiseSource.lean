import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryOneWayTaggedStationaryUniformAverageSource
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance referenceCrossBoundaryOneWayTaggedStationaryUniformPointwiseSourceSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- A pointwise uniform bound on the genuine stationary comparison source
closes the normalized source-average hypothesis automatically.

The source envelope is taken to be `C.sourceBound` itself, so the only new
substantive input beyond the stationary comparison data is the pointwise
volume-independent source bound.  This remains an interface theorem: it does
not identify the finite positive-weight comparison data with the full
four-dimensional Wilson conditional law, and it does not assert physical
Poincare/coercivity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_averageExpectationDiscrepancy_singleton_le_uniformPointwiseSourceResolvent_add_expSweepResidual
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
    (sourceAverageBound : ℝ)
    (hSourcePointwise : ∀ source,
      C.sourceBound source ≤ sourceAverageBound)
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
  classical
  have hCardNat :
      0 <
        Fintype.card
          (Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H)) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTaggedIndex_card_pos
      H
  let source0 :
      Sum
        (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) :=
    Classical.choice (Fintype.card_pos_iff.mp hCardNat)
  have hSourceAverageNonneg : 0 ≤ sourceAverageBound :=
    (C.sourceBound_nonneg source0).trans (hSourcePointwise source0)
  have hSourceAverage :
      finiteProductVariationTotal C.sourceBound ≤
        (Fintype.card
          (Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ) *
          sourceAverageBound := by
    unfold finiteProductVariationTotal
    calc
      (∑ source :
          Sum
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (PeriodicHypercubicEvenSpatialSliceLink H),
        C.sourceBound source) ≤
          ∑ _source :
            Sum
              (PeriodicHypercubicEvenSpatialSliceLink H)
              (PeriodicHypercubicEvenSpatialSliceLink H),
            sourceAverageBound := by
        apply Finset.sum_le_sum
        intro source _hSource
        exact hSourcePointwise source
      _ =
          (Fintype.card
            (Sum
              (PeriodicHypercubicEvenSpatialSliceLink H)
              (PeriodicHypercubicEvenSpatialSliceLink H)) : ℝ) *
            sourceAverageBound := by
        simp
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryOneWayTagged_averageExpectationDiscrepancy_singleton_le_uniformAverageSourceResolvent_add_expSweepResidual
      H beta hbeta hBetaLt f P C hDomination C.sourceBound
      C.sourceBound_nonneg (fun _ => le_rfl)
      sourceAverageBound hSourceAverageNonneg hSourceAverage
      magnitude hMagnitude hSingleton sweeps

end

end MathlibAnalytic
end MGAP4D
