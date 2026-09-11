import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorActualRandomScanHammingContractionCanonical
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorActualRandomScanHammingContractionIteration

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Canonical all-volume n-step actual Perron-posterior random-scan overlap
coupling from an arbitrary exact initial coupling.  This is an auxiliary
heat-bath construction and remains distinct from geometric one-slab transfer
dynamics. -/
noncomputable def
    finiteEvenFourTorusZ2PerronPosteriorActualRandomScanOverlapCouplingIterateData
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
    {leftLaw rightLaw :
      FiniteRealProbabilityData
        (FiniteEvenFourTorusZ2SliceConfiguration H)}
    (initial : FiniteRealCouplingData leftLaw rightLaw)
    (n : ℕ) :=
  (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy).randomScanOverlapCouplingIterateData
    β hβ hβCutoff H environment initial n

/-- Canonical all-volume n-step expected-Hamming contraction with the exact
power of the actual random-scan heat-bath rate.  No geometric one-slab
gap identification is made. -/
theorem
    finiteEvenFourTorusZ2PerronPosteriorActualRandomScanIterateExpectedHamming_le
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
    {leftLaw rightLaw :
      FiniteRealProbabilityData
        (FiniteEvenFourTorusZ2SliceConfiguration H)}
    (initial : FiniteRealCouplingData leftLaw rightLaw)
    (n : ℕ) :
    (finiteEvenFourTorusZ2PerronPosteriorActualRandomScanOverlapCouplingIterateData
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H environment
      initial n).expectedCost finiteProductHammingDistanceReal ≤
      finiteEvenFourTorusZ2PerronPosteriorActualRandomScanHammingRate
          energyIdentity energyNontrivial hEnergy β hβ hβCutoff H ^ n *
        initial.expectedCost finiteProductHammingDistanceReal := by
  exact
    (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy).randomScanOverlapCouplingIterate_expectedHamming_le_pow_mul
        β hβ hβCutoff H environment initial n

end
end MathlibAnalytic
end MGAP4D
