import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorActualRandomScanHammingContractionCanonical
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorActualRandomScanStationaryMixing

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Canonical all-volume stationary Perron-smoothed posterior probability law
for the auxiliary actual random-scan heat-bath kernel. -/
noncomputable def
    finiteEvenFourTorusZ2PerronPosteriorActualRandomScanStationaryProbabilityData
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤
        (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
          energyIdentity energyNontrivial hEnergy).couplingCutoff)
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :=
  (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy).randomScanStationaryProbabilityData
    β hβ hβCutoff H environment

/-- Canonical all-volume n-step overlap coupling from an arbitrary finite
initial law to the stationary actual Perron-smoothed posterior orbit.  This is
auxiliary heat-bath dynamics and remains distinct from geometric one-slab
transfer dynamics. -/
noncomputable def
    finiteEvenFourTorusZ2PerronPosteriorActualRandomScanToStationaryOverlapCouplingIterateData
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
    (n : ℕ) :=
  (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy).randomScanToStationaryOverlapCouplingIterateData
    β hβ hβCutoff H environment initialLaw n

/-- Canonical all-volume actual random-scan expected-Hamming mixing bound from
an arbitrary finite initial law to the stationary posterior.  The rate is the
explicit heat-bath coupling rate and is not a geometric one-slab transfer
rate. -/
theorem
    finiteEvenFourTorusZ2PerronPosteriorActualRandomScanToStationaryIterateExpectedHamming_le
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
    (finiteEvenFourTorusZ2PerronPosteriorActualRandomScanToStationaryOverlapCouplingIterateData
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H environment
      initialLaw n).expectedCost finiteProductHammingDistanceReal ≤
      finiteEvenFourTorusZ2PerronPosteriorActualRandomScanHammingRate
          energyIdentity energyNontrivial hEnergy β hβ hβCutoff H ^ n *
        (Fintype.card (FiniteEvenFourTorusSpatialLink H) : ℝ) := by
  exact
    (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy).randomScanToStationaryOverlapCouplingIterate_expectedHamming_le_pow_mul_card
        β hβ hβCutoff H environment initialLaw n

/-- Canonical all-volume convergence of every real Hamming `1`-Lipschitz
observable from an arbitrary finite initial law to the actual Perron-smoothed
posterior expectation. -/
theorem
    finiteEvenFourTorusZ2PerronPosteriorActualRandomScanIterateExpectation_sub_posterior_abs_le
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
    (n : ℕ)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (hLipschitz : FiniteProductHammingOneLipschitz f) :
    |(finiteRealProbabilityKernelIterateData
        (finitePositiveWeightRandomScanProbabilityData
          (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
            H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
          ((finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
            energyIdentity energyNontrivial hEnergy).posteriorWeight_pos
              β hβ hβCutoff H environment)
          (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H))
        n initialLaw).expectation f -
      finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
        H β energyIdentity energyNontrivial hβ hEnergy environment f| ≤
      finiteEvenFourTorusZ2PerronPosteriorActualRandomScanHammingRate
          energyIdentity energyNontrivial hEnergy β hβ hβCutoff H ^ n *
        (Fintype.card (FiniteEvenFourTorusSpatialLink H) : ℝ) := by
  exact
    (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy).randomScanIterate_expectation_sub_posterior_abs_le_pow_mul_card
        β hβ hβCutoff H environment initialLaw n f hLipschitz

end
end MathlibAnalytic
end MGAP4D
