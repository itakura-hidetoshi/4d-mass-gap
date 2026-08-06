import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorActualRandomScanStationaryMixingCanonical
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorActualRandomScanTotalVariationMixing

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Canonical all-volume auxiliary random-scan convergence in unhalved `L¹`
distance from an arbitrary finite initial law to the actual fixed-environment
Perron-smoothed posterior.  The explicit heat-bath rate remains distinct from
the geometric one-slab transfer rate. -/
theorem
    finiteEvenFourTorusZ2PerronPosteriorActualRandomScanIterateL1Distance_le
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤
        (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
          energyIdentity energyNontrivial hEnergy).couplingCutoff)
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
        ((finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
          energyIdentity energyNontrivial hEnergy).posteriorWeight_pos
            β hβ hβCutoff H environment)
        (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H))
      n initialLaw).l1Distance
        (finiteEvenFourTorusZ2PerronPosteriorActualRandomScanStationaryProbabilityData
          energyIdentity energyNontrivial hEnergy β hβ hβCutoff H environment) ≤
      2 *
        (finiteEvenFourTorusZ2PerronPosteriorActualRandomScanHammingRate
            energyIdentity energyNontrivial hEnergy β hβ hβCutoff H ^ n *
          (Fintype.card (FiniteEvenFourTorusSpatialLink H) : ℝ)) := by
  exact
    (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy).randomScanIterate_l1Distance_posterior_le_two_mul_pow_mul_card
        β hβ hβCutoff H environment initialLaw n

/-- Canonical all-volume auxiliary random-scan convergence in standard
total-variation distance from an arbitrary finite initial law to the actual
fixed-environment Perron-smoothed posterior, without a full-configuration
cardinality loss. -/
theorem
    finiteEvenFourTorusZ2PerronPosteriorActualRandomScanIterateTotalVariationDistance_le
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤
        (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
          energyIdentity energyNontrivial hEnergy).couplingCutoff)
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
        ((finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
          energyIdentity energyNontrivial hEnergy).posteriorWeight_pos
            β hβ hβCutoff H environment)
        (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H))
      n initialLaw).totalVariationDistance
        (finiteEvenFourTorusZ2PerronPosteriorActualRandomScanStationaryProbabilityData
          energyIdentity energyNontrivial hEnergy β hβ hβCutoff H environment) ≤
      finiteEvenFourTorusZ2PerronPosteriorActualRandomScanHammingRate
          energyIdentity energyNontrivial hEnergy β hβ hβCutoff H ^ n *
        (Fintype.card (FiniteEvenFourTorusSpatialLink H) : ℝ) := by
  exact
    (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy).randomScanIterate_totalVariationDistance_posterior_le_pow_mul_card
        β hβ hβCutoff H environment initialLaw n

end
end MathlibAnalytic
end MGAP4D
