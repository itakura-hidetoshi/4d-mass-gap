import MGAP4D.MathlibAnalytic.FinitePositiveWeightStationaryCrossWeightComparison
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedBoundaryComparisonIteration
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedBoundaryRandomScanComparison
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Actual stationary comparison for the two encoded reduced augmented
positive weights associated with upper boundaries differing at one source
link.  The residual is the expectation discrepancy after one auxiliary Gibbs
random-scan step for the replaced boundary. -/
theorem FiniteProductVariationBound.finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryExpectation_difference_abs_le_sourcePairing_add_randomScanResidual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    {f : FiniteEvenFourTorusZ2AugmentedConfiguration H → ℝ}
    (P : FiniteProductVariationBound f)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    |finitePositiveWeightExpectation
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
            H β energyIdentity energyNontrivial hβ hEnergy B)
          f -
        finitePositiveWeightExpectation
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
            H β energyIdentity energyNontrivial hβ hEnergy
            (finiteZ2GaugeReplaceCoordinate B source g))
          f| ≤
      (Fintype.card
          (FiniteEvenFourTorusZ2AugmentedCoordinate H) : ℝ)⁻¹ *
          ∑ target : FiniteEvenFourTorusZ2AugmentedCoordinate H,
            finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound
                H β energyIdentity energyNontrivial source target *
              P.variation target +
        |finitePositiveWeightExpectation
            (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
              H β energyIdentity energyNontrivial hβ hEnergy B)
            (finitePositiveWeightRandomScanConditionalExpectation
              (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
                H β energyIdentity energyNontrivial hβ hEnergy
                (finiteZ2GaugeReplaceCoordinate B source g))
              f) -
          finitePositiveWeightExpectation
            (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
              H β energyIdentity energyNontrivial hβ hEnergy
              (finiteZ2GaugeReplaceCoordinate B source g))
            (finitePositiveWeightRandomScanConditionalExpectation
              (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
                H β energyIdentity energyNontrivial hβ hEnergy
                (finiteZ2GaugeReplaceCoordinate B source g))
              f)| := by
  apply
    P.expectation_crossWeight_difference_abs_le_sourcePairing_add_randomScanResidual
  · intro X
    exact
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_pos
        H β energyIdentity energyNontrivial hβ hEnergy B X
  · intro X
    exact
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_pos
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteZ2GaugeReplaceCoordinate B source g) X
  · intro target
    exact
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy source target
  · intro X target
    exact
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryConditionalCrossL1_le_sourceBound
        H β energyIdentity energyNontrivial hβ hEnergy source g B X target

/-- Exact three-coordinate form of the actual stationary one-step comparison
source. -/
theorem FiniteProductVariationBound.finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryExpectation_difference_abs_le_threeCoordinateSource_add_randomScanResidual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    {f : FiniteEvenFourTorusZ2AugmentedConfiguration H → ℝ}
    (P : FiniteProductVariationBound f)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    |finitePositiveWeightExpectation
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
            H β energyIdentity energyNontrivial hβ hEnergy B)
          f -
        finitePositiveWeightExpectation
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
            H β energyIdentity energyNontrivial hβ hEnergy
            (finiteZ2GaugeReplaceCoordinate B source g))
          f| ≤
      (Fintype.card
          (FiniteEvenFourTorusZ2AugmentedCoordinate H) : ℝ)⁻¹ *
          (2 *
              (1 - Real.exp
                (-2 * β * (energyNontrivial - energyIdentity))) *
            ∑ target ∈
              finiteEvenFourTorusZ2AugmentedBoundarySourceSupport H source,
                P.variation target) +
        |finitePositiveWeightExpectation
            (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
              H β energyIdentity energyNontrivial hβ hEnergy B)
            (finitePositiveWeightRandomScanConditionalExpectation
              (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
                H β energyIdentity energyNontrivial hβ hEnergy
                (finiteZ2GaugeReplaceCoordinate B source g))
              f) -
          finitePositiveWeightExpectation
            (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
              H β energyIdentity energyNontrivial hβ hEnergy
              (finiteZ2GaugeReplaceCoordinate B source g))
            (finitePositiveWeightRandomScanConditionalExpectation
              (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
                H β energyIdentity energyNontrivial hβ hEnergy
                (finiteZ2GaugeReplaceCoordinate B source g))
              f)| := by
  rw [←
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound_pairing_eq
      H β energyIdentity energyNontrivial source P.variation]
  exact
    P.finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryExpectation_difference_abs_le_sourcePairing_add_randomScanResidual
      H β energyIdentity energyNontrivial hβ hEnergy source g B

end

end MathlibAnalytic
end MGAP4D
