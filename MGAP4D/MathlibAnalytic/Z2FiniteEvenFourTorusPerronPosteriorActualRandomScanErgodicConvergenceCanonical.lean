import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorActualRandomScanErgodicConvergence
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorActualRandomScanTotalVariationMixingCanonical

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Canonical all-volume convergence in unhalved `L¹` distance from every
finite initial law to the actual fixed-environment Perron-smoothed posterior
under the auxiliary random-scan heat-bath kernel.  This does not identify the
heat-bath rate with a geometric one-slab transfer gap. -/
theorem
    finiteEvenFourTorusZ2PerronPosteriorActualRandomScanIterateL1Distance_tendsto_zero
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
        (FiniteEvenFourTorusZ2SliceConfiguration H)) :
    Tendsto
      (fun n : ℕ =>
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
              energyIdentity energyNontrivial hEnergy β hβ hβCutoff H
              environment))
      atTop (nhds 0) := by
  exact
    (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy).randomScanIterate_l1Distance_posterior_tendsto_zero
        β hβ hβCutoff H environment initialLaw

/-- Canonical all-volume convergence in standard total-variation distance
from every finite initial law to the actual fixed-environment Perron-smoothed
posterior under the auxiliary random-scan heat-bath kernel. -/
theorem
    finiteEvenFourTorusZ2PerronPosteriorActualRandomScanIterateTotalVariationDistance_tendsto_zero
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
        (FiniteEvenFourTorusZ2SliceConfiguration H)) :
    Tendsto
      (fun n : ℕ =>
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
              energyIdentity energyNontrivial hEnergy β hβ hβCutoff H
              environment))
      atTop (nhds 0) := by
  exact
    (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy).randomScanIterate_totalVariationDistance_posterior_tendsto_zero
        β hβ hβCutoff H environment initialLaw

end
end MathlibAnalytic
end MGAP4D
