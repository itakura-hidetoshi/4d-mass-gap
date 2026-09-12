import MGAP4D.MathlibAnalytic.FinitePositiveWeightRandomScanOverlapCouplingIteration
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorActualRandomScanHammingContraction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance finiteEvenFourTorusSpatialLinkNonemptyForActualRandomScanIteration
    (H : ℕ) : Nonempty (FiniteEvenFourTorusSpatialLink H) :=
  ⟨(⟨0, by simp⟩, ⟨1, by norm_num⟩)⟩

namespace Z2PerronPosteriorActualHighTemperatureContinuationData

/-- Iterate the actual fixed-environment Perron-posterior random-scan overlap
coupling from any exact initial coupling.  This is auxiliary heat-bath
coupling dynamics and does not identify its rate with the geometric one-slab
transfer gap. -/
noncomputable def randomScanOverlapCouplingIterateData
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    {leftLaw rightLaw :
      FiniteRealProbabilityData
        (FiniteEvenFourTorusZ2SliceConfiguration H)}
    (initial : FiniteRealCouplingData leftLaw rightLaw)
    (n : ℕ) :
    FiniteRealCouplingData
      (finiteRealProbabilityKernelIterateData
        (finitePositiveWeightRandomScanProbabilityData
          (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
            H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
          (C.posteriorWeight_pos β hβ hβCutoff H environment)
          (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H))
        n leftLaw)
      (finiteRealProbabilityKernelIterateData
        (finitePositiveWeightRandomScanProbabilityData
          (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
            H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
          (C.posteriorWeight_pos β hβ hβCutoff H environment)
          (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H))
        n rightLaw) :=
  finitePositiveWeightRandomScanOverlapCouplingIterateData
    (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
      H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
    (C.posteriorWeight_pos β hβ hβCutoff H environment)
    (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H)
    initial n

/-- The actual iterated Perron-posterior random-scan overlap coupling contracts
expected Hamming cost by the exact power of the explicit heat-bath rate.  No
geometric one-slab transfer-gap identification is made. -/
theorem randomScanOverlapCouplingIterate_expectedHamming_le_pow_mul
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    {leftLaw rightLaw :
      FiniteRealProbabilityData
        (FiniteEvenFourTorusZ2SliceConfiguration H)}
    (initial : FiniteRealCouplingData leftLaw rightLaw)
    (n : ℕ) :
    (C.randomScanOverlapCouplingIterateData
        β hβ hβCutoff H environment initial n).expectedCost
      finiteProductHammingDistanceReal ≤
      C.randomScanHammingRate β hβ hβCutoff H ^ n *
        initial.expectedCost finiteProductHammingDistanceReal := by
  let B := C.toBidirectionalDobrushinData
    β hβ hβCutoff H environment
  have h :=
    B.randomScanOverlapCouplingIterate_expectedHamming_le_pow_mul
      (C.posteriorWeight_pos β hβ hβCutoff H environment)
      (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H)
      initial n
  simpa [randomScanOverlapCouplingIterateData, randomScanHammingRate,
    finitePositiveWeightBidirectionalRandomScanHammingRate,
    finitePositiveWeightBidirectionalCouplingHeatBathGap, B] using h

end Z2PerronPosteriorActualHighTemperatureContinuationData

end
end MathlibAnalytic
end MGAP4D
