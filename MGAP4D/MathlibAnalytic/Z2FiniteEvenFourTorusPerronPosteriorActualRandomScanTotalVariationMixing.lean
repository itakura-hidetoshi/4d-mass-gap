import MGAP4D.MathlibAnalytic.FiniteRealProbabilityCouplingTotalVariation
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorActualRandomScanStationaryMixing
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance finiteEvenFourTorusSpatialLinkNonemptyForActualRandomScanTotalVariationMixing
    (H : ℕ) : Nonempty (FiniteEvenFourTorusSpatialLink H) :=
  ⟨(⟨0, by simp⟩, ⟨1, by norm_num⟩)⟩

namespace Z2PerronPosteriorActualHighTemperatureContinuationData

/-- Actual fixed-environment auxiliary random-scan convergence in unhalved
`L¹` distance from an arbitrary finite initial law to the Perron-smoothed
posterior.  The rate is the explicit heat-bath coupling rate and remains
distinct from the geometric one-slab transfer rate. -/
theorem randomScanIterate_l1Distance_posterior_le_two_mul_pow_mul_card
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (initialLaw :
      FiniteRealProbabilityData
        (FiniteEvenFourTorusZ2SliceConfiguration H))
    (n : ℕ) :
    (finiteRealProbabilityKernelIterateData
      (finitePositiveWeightRandomScanProbabilityData
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
        (C.posteriorWeight_pos β hβ hβCutoff H environment)
        (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H))
      n initialLaw).l1Distance
        (C.randomScanStationaryProbabilityData
          β hβ hβCutoff H environment) ≤
      2 * (C.randomScanHammingRate β hβ hβCutoff H ^ n *
        (Fintype.card (FiniteEvenFourTorusSpatialLink H) : ℝ)) := by
  let B := C.toBidirectionalDobrushinData
    β hβ hβCutoff H environment
  have h :=
    B.randomScanIterate_l1Distance_stationary_le_two_mul_pow_mul_card
      (C.posteriorWeight_pos β hβ hβCutoff H environment)
      (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H)
      initialLaw n
  simpa [randomScanStationaryProbabilityData, randomScanHammingRate,
    finitePositiveWeightBidirectionalRandomScanHammingRate,
    finitePositiveWeightBidirectionalCouplingHeatBathGap, B] using h

/-- Actual fixed-environment auxiliary random-scan convergence in standard
total-variation distance from an arbitrary finite initial law to the
Perron-smoothed posterior, with no full-configuration cardinality loss. -/
theorem randomScanIterate_totalVariationDistance_posterior_le_pow_mul_card
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (initialLaw :
      FiniteRealProbabilityData
        (FiniteEvenFourTorusZ2SliceConfiguration H))
    (n : ℕ) :
    (finiteRealProbabilityKernelIterateData
      (finitePositiveWeightRandomScanProbabilityData
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
        (C.posteriorWeight_pos β hβ hβCutoff H environment)
        (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H))
      n initialLaw).totalVariationDistance
        (C.randomScanStationaryProbabilityData
          β hβ hβCutoff H environment) ≤
      C.randomScanHammingRate β hβ hβCutoff H ^ n *
        (Fintype.card (FiniteEvenFourTorusSpatialLink H) : ℝ) := by
  let B := C.toBidirectionalDobrushinData
    β hβ hβCutoff H environment
  have h :=
    B.randomScanIterate_totalVariationDistance_stationary_le_pow_mul_card
      (C.posteriorWeight_pos β hβ hβCutoff H environment)
      (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H)
      initialLaw n
  simpa [randomScanStationaryProbabilityData, randomScanHammingRate,
    finitePositiveWeightBidirectionalRandomScanHammingRate,
    finitePositiveWeightBidirectionalCouplingHeatBathGap, B] using h

end Z2PerronPosteriorActualHighTemperatureContinuationData

end
end MathlibAnalytic
end MGAP4D
