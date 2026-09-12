import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorActualRandomScanStationaryMixingCanonical
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorActualRandomScanStationaryUniqueness

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Canonical all-volume equality of every Hamming `1`-Lipschitz observable
under an arbitrary stationary finite law and the actual fixed-environment
Perron-smoothed posterior.  This concerns only the auxiliary random-scan
heat-bath kernel and does not identify its rate with the geometric one-slab
transfer gap. -/
theorem
    finiteEvenFourTorusZ2PerronPosteriorActualRandomScanStationaryExpectation_eq
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
    (law :
      FiniteRealProbabilityData
        (FiniteEvenFourTorusZ2SliceConfiguration H))
    (hStationary :
      law.IsStationaryForKernel
        (finitePositiveWeightRandomScanProbabilityData
          (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
            H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
          ((finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
            energyIdentity energyNontrivial hEnergy).posteriorWeight_pos
              β hβ hβCutoff H environment)
          (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H)))
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (hLipschitz : FiniteProductHammingOneLipschitz f) :
    law.expectation f =
      finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
        H β energyIdentity energyNontrivial hβ hEnergy environment f := by
  exact
    (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy).randomScan_stationary_expectation_eq_posterior
        β hβ hβCutoff H environment law hStationary f hLipschitz

/-- Canonical all-volume uniqueness of the actual fixed-environment
Perron-smoothed posterior among finite laws stationary for its strict
auxiliary random-scan heat-bath kernel. -/
theorem
    finiteEvenFourTorusZ2PerronPosteriorActualRandomScanStationaryLaw_eq
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
    (law :
      FiniteRealProbabilityData
        (FiniteEvenFourTorusZ2SliceConfiguration H))
    (hStationary :
      law.IsStationaryForKernel
        (finitePositiveWeightRandomScanProbabilityData
          (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
            H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
          ((finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
            energyIdentity energyNontrivial hEnergy).posteriorWeight_pos
              β hβ hβCutoff H environment)
          (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H))) :
    law =
      finiteEvenFourTorusZ2PerronPosteriorActualRandomScanStationaryProbabilityData
        energyIdentity energyNontrivial hEnergy β hβ hβCutoff H environment := by
  exact
    (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy).randomScan_stationary_law_eq_posteriorProbabilityData
        β hβ hβCutoff H environment law hStationary

/-- Canonical all-volume equality of any two finite laws stationary for the
same actual fixed-environment auxiliary random-scan heat-bath kernel. -/
theorem
    finiteEvenFourTorusZ2PerronPosteriorActualRandomScanStationaryLaws_unique
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
    (leftLaw rightLaw :
      FiniteRealProbabilityData
        (FiniteEvenFourTorusZ2SliceConfiguration H))
    (hLeftStationary :
      leftLaw.IsStationaryForKernel
        (finitePositiveWeightRandomScanProbabilityData
          (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
            H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
          ((finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
            energyIdentity energyNontrivial hEnergy).posteriorWeight_pos
              β hβ hβCutoff H environment)
          (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H)))
    (hRightStationary :
      rightLaw.IsStationaryForKernel
        (finitePositiveWeightRandomScanProbabilityData
          (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
            H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
          ((finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
            energyIdentity energyNontrivial hEnergy).posteriorWeight_pos
              β hβ hβCutoff H environment)
          (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H))) :
    leftLaw = rightLaw := by
  exact
    (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy).randomScan_stationary_laws_unique
        β hβ hβCutoff H environment leftLaw rightLaw
        hLeftStationary hRightStationary

end
end MathlibAnalytic
end MGAP4D
