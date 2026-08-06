import MGAP4D.MathlibAnalytic.FinitePositiveWeightRandomScanStationaryUniqueness
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorActualRandomScanStationaryMixing
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance finiteEvenFourTorusSpatialLinkNonemptyForActualRandomScanStationaryUniqueness
    (H : ℕ) : Nonempty (FiniteEvenFourTorusSpatialLink H) :=
  ⟨(⟨0, by simp⟩, ⟨1, by norm_num⟩)⟩

namespace Z2PerronPosteriorActualHighTemperatureContinuationData

/-- Every finite law stationary for the actual fixed-environment auxiliary
random-scan heat-bath kernel agrees with the Perron-smoothed posterior on all
real Hamming `1`-Lipschitz observables.  This is not a statement about the
geometric one-slab transfer evolution. -/
theorem randomScan_stationary_expectation_eq_posterior
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
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
          (C.posteriorWeight_pos β hβ hβCutoff H environment)
          (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H)))
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (hLipschitz : FiniteProductHammingOneLipschitz f) :
    law.expectation f =
      finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
        H β energyIdentity energyNontrivial hβ hEnergy environment f := by
  let B := C.toBidirectionalDobrushinData
    β hβ hβCutoff H environment
  have h :=
    B.randomScan_stationary_expectation_eq_globalExpectation
      (C.posteriorWeight_pos β hβ hβCutoff H environment)
      (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H)
      law hStationary f hLipschitz
  simpa [finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation, B] using h

/-- The actual fixed-environment Perron-smoothed posterior is the unique
finite real probability law stationary for its strict auxiliary random-scan
heat-bath kernel. -/
theorem randomScan_stationary_law_eq_posteriorProbabilityData
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
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
          (C.posteriorWeight_pos β hβ hβCutoff H environment)
          (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H))) :
    law = C.randomScanStationaryProbabilityData
      β hβ hβCutoff H environment := by
  let B := C.toBidirectionalDobrushinData
    β hβ hβCutoff H environment
  have h :=
    B.randomScan_stationary_law_eq_globalProbabilityData
      (C.posteriorWeight_pos β hβ hβCutoff H environment)
      (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H)
      law hStationary
  simpa [randomScanStationaryProbabilityData, B] using h

/-- Any two finite laws stationary for the same actual fixed-environment
random-scan heat-bath kernel are equal. -/
theorem randomScan_stationary_laws_unique
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
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
          (C.posteriorWeight_pos β hβ hβCutoff H environment)
          (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H)))
    (hRightStationary :
      rightLaw.IsStationaryForKernel
        (finitePositiveWeightRandomScanProbabilityData
          (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
            H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
          (C.posteriorWeight_pos β hβ hβCutoff H environment)
          (finiteEvenFourTorusSpatialLink_card_pos_for_actualRandomScan H))) :
    leftLaw = rightLaw := by
  rw [C.randomScan_stationary_law_eq_posteriorProbabilityData
      β hβ hβCutoff H environment leftLaw hLeftStationary,
    C.randomScan_stationary_law_eq_posteriorProbabilityData
      β hβ hβCutoff H environment rightLaw hRightStationary]

end Z2PerronPosteriorActualHighTemperatureContinuationData

end
end MathlibAnalytic
end MGAP4D
