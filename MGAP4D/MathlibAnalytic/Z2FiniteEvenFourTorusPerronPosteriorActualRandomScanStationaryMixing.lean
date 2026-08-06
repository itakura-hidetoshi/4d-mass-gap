import MGAP4D.MathlibAnalytic.FinitePositiveWeightRandomScanStationaryMixing
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorActualRandomScanHammingContraction
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorObservablePathResponse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance finiteEvenFourTorusSpatialLinkNonemptyForActualRandomScanStationaryMixing
    (H : ℕ) : Nonempty (FiniteEvenFourTorusSpatialLink H) :=
  ⟨(⟨0, by simp⟩, ⟨1, by norm_num⟩)⟩

namespace Z2PerronPosteriorActualHighTemperatureContinuationData

/-- The actual fixed-environment Perron-smoothed posterior packaged as the
stationary normalized Gibbs law for its auxiliary random-scan heat-bath
kernel. -/
noncomputable def randomScanStationaryProbabilityData
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FiniteRealProbabilityData
      (FiniteEvenFourTorusZ2SliceConfiguration H) :=
  finitePositiveWeightGlobalProbabilityData
    (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
      H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
    (C.posteriorWeight_pos β hβ hβCutoff H environment)

/-- Iterate the actual fixed-environment random-scan overlap coupling from an
arbitrary finite initial law to the stationary Perron-smoothed posterior
orbit.  This remains auxiliary heat-bath dynamics and is not the geometric
one-slab transfer evolution. -/
noncomputable def randomScanToStationaryOverlapCouplingIterateData
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
    FiniteRealCouplingData
      (finiteRealProbabilityKernelIterateData
        (finitePositiveWeightRandomScanProbabilityData
          (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
            H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
          (C.posteriorWeight_pos β hβ hβCutoff H environment)
          (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H))
        n initialLaw)
      (finiteRealProbabilityKernelIterateData
        (finitePositiveWeightRandomScanProbabilityData
          (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
            H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
          (C.posteriorWeight_pos β hβ hβCutoff H environment)
          (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H))
        n (C.randomScanStationaryProbabilityData
          β hβ hβCutoff H environment)) :=
  finitePositiveWeightRandomScanToStationaryOverlapCouplingIterateData
    (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
      H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
    (C.posteriorWeight_pos β hβ hβCutoff H environment)
    (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H)
    initialLaw n

/-- Actual fixed-environment random-scan expected-Hamming mixing from an
arbitrary finite initial law to the stationary Perron-smoothed posterior,
with the exact power of the explicit heat-bath rate. -/
theorem randomScanToStationaryOverlapCouplingIterate_expectedHamming_le_pow_mul_card
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
    (C.randomScanToStationaryOverlapCouplingIterateData
      β hβ hβCutoff H environment initialLaw n).expectedCost
        finiteProductHammingDistanceReal ≤
      C.randomScanHammingRate β hβ hβCutoff H ^ n *
        (Fintype.card (FiniteEvenFourTorusSpatialLink H) : ℝ) := by
  let B := C.toBidirectionalDobrushinData
    β hβ hβCutoff H environment
  have h :=
    B.randomScanToStationaryOverlapCouplingIterate_expectedHamming_le_pow_mul_card
      (C.posteriorWeight_pos β hβ hβCutoff H environment)
      (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H)
      initialLaw n
  simpa [randomScanToStationaryOverlapCouplingIterateData,
    randomScanStationaryProbabilityData, randomScanHammingRate,
    finitePositiveWeightBidirectionalRandomScanHammingRate,
    finitePositiveWeightBidirectionalCouplingHeatBathGap, B] using h

/-- Every real Hamming `1`-Lipschitz observable under the actual fixed-
environment random-scan orbit converges to the Perron-smoothed posterior
expectation at the explicit heat-bath rate. -/
theorem randomScanIterate_expectation_sub_posterior_abs_le_pow_mul_card
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
    (n : ℕ)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (hLipschitz : FiniteProductHammingOneLipschitz f) :
    |(finiteRealProbabilityKernelIterateData
        (finitePositiveWeightRandomScanProbabilityData
          (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
            H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
          (C.posteriorWeight_pos β hβ hβCutoff H environment)
          (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H))
        n initialLaw).expectation f -
      finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
        H β energyIdentity energyNontrivial hβ hEnergy environment f| ≤
      C.randomScanHammingRate β hβ hβCutoff H ^ n *
        (Fintype.card (FiniteEvenFourTorusSpatialLink H) : ℝ) := by
  let B := C.toBidirectionalDobrushinData
    β hβ hβCutoff H environment
  have h :=
    B.randomScanIterate_expectation_sub_global_abs_le_pow_mul_card
      (C.posteriorWeight_pos β hβ hβCutoff H environment)
      (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H)
      initialLaw n f hLipschitz
  simpa [finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation,
    randomScanHammingRate,
    finitePositiveWeightBidirectionalRandomScanHammingRate,
    finitePositiveWeightBidirectionalCouplingHeatBathGap, B] using h

end Z2PerronPosteriorActualHighTemperatureContinuationData

end
end MathlibAnalytic
end MGAP4D
