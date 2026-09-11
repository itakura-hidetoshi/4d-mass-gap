import MGAP4D.MathlibAnalytic.FinitePositiveWeightRandomScanErgodicConvergence
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorActualRandomScanTotalVariationMixing
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

local instance finiteEvenFourTorusSpatialLinkNonemptyForActualRandomScanErgodicConvergence
    (H : ℕ) : Nonempty (FiniteEvenFourTorusSpatialLink H) :=
  ⟨(⟨0, by simp⟩, ⟨1, by norm_num⟩)⟩

namespace Z2PerronPosteriorActualHighTemperatureContinuationData

/-- For the actual fixed-environment auxiliary random-scan heat-bath kernel,
the unhalved `L¹` distance from every finite initial law to the
Perron-smoothed posterior tends to zero.  This remains distinct from any
geometric one-slab transfer convergence statement. -/
theorem randomScanIterate_l1Distance_posterior_tendsto_zero
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
        (FiniteEvenFourTorusZ2SliceConfiguration H)) :
    Tendsto
      (fun n : ℕ =>
        (finiteRealProbabilityKernelIterateData
          (finitePositiveWeightRandomScanProbabilityData
            (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
              H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
            (C.posteriorWeight_pos β hβ hβCutoff H environment)
            (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H))
          n initialLaw).l1Distance
            (C.randomScanStationaryProbabilityData
              β hβ hβCutoff H environment))
      atTop (nhds 0) := by
  let B := C.toBidirectionalDobrushinData
    β hβ hβCutoff H environment
  have h :=
    B.randomScanIterate_l1Distance_stationary_tendsto_zero
      (C.posteriorWeight_pos β hβ hβCutoff H environment)
      (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H)
      initialLaw
  simpa [randomScanStationaryProbabilityData, B] using h

/-- For the actual fixed-environment auxiliary random-scan heat-bath kernel,
the standard total-variation distance from every finite initial law to the
Perron-smoothed posterior tends to zero. -/
theorem randomScanIterate_totalVariationDistance_posterior_tendsto_zero
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
        (FiniteEvenFourTorusZ2SliceConfiguration H)) :
    Tendsto
      (fun n : ℕ =>
        (finiteRealProbabilityKernelIterateData
          (finitePositiveWeightRandomScanProbabilityData
            (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
              H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
            (C.posteriorWeight_pos β hβ hβCutoff H environment)
            (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H))
          n initialLaw).totalVariationDistance
            (C.randomScanStationaryProbabilityData
              β hβ hβCutoff H environment))
      atTop (nhds 0) := by
  let B := C.toBidirectionalDobrushinData
    β hβ hβCutoff H environment
  have h :=
    B.randomScanIterate_totalVariationDistance_stationary_tendsto_zero
      (C.posteriorWeight_pos β hβ hβCutoff H environment)
      (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H)
      initialLaw
  simpa [randomScanStationaryProbabilityData, B] using h

end Z2PerronPosteriorActualHighTemperatureContinuationData

end
end MathlibAnalytic
end MGAP4D
