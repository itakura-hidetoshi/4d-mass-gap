import MGAP4D.MathlibAnalytic.FinitePositiveWeightStationaryRandomScanComparison
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedBoundaryComparisonIteration
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedBoundaryRandomScanComparison
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Encoded reduced augmented weight at one fixed upper boundary. -/
abbrev finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryWeight
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :=
  finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
    H β energyIdentity energyNontrivial hβ hEnergy B

/-- Normalized expectation for the encoded reduced augmented weight at one
fixed upper boundary. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryExpectation
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (f : FiniteEvenFourTorusZ2AugmentedConfiguration H → ℝ) : ℝ :=
  finitePositiveWeightGlobalExpectation
    (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryWeight
      H β energyIdentity energyNontrivial hβ hEnergy B) f

/-- Auxiliary exact Gibbs random-scan operator at one fixed upper boundary. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryRandomScan
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (f : FiniteEvenFourTorusZ2AugmentedConfiguration H → ℝ) :
    FiniteEvenFourTorusZ2AugmentedConfiguration H → ℝ :=
  finitePositiveWeightRandomScanConditionalExpectation
    (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryWeight
      H β energyIdentity energyNontrivial hβ hEnergy B) f

/-- The actual encoded augmented coordinate type is nonempty. -/
theorem finiteEvenFourTorusZ2AugmentedCoordinate_card_pos
    (H : ℕ) :
    0 < Fintype.card (FiniteEvenFourTorusZ2AugmentedCoordinate H) := by
  let v : FiniteEvenFourTorusSpatialVertex H := ⟨0, by simp⟩
  exact Fintype.card_pos_iff.mpr ⟨Sum.inl v⟩

/-- Actual stationary comparison for upper boundaries differing at one source
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
    |finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryExpectation
          H β energyIdentity energyNontrivial hβ hEnergy B f -
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryExpectation
          H β energyIdentity energyNontrivial hβ hEnergy
          (finiteZ2GaugeReplaceCoordinate B source g) f| ≤
      (Fintype.card (FiniteEvenFourTorusZ2AugmentedCoordinate H) : ℝ)⁻¹ *
          ∑ target : FiniteEvenFourTorusZ2AugmentedCoordinate H,
            finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound
                H β energyIdentity energyNontrivial source target *
              P.variation target +
        |finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryExpectation
              H β energyIdentity energyNontrivial hβ hEnergy B
              (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryRandomScan
                H β energyIdentity energyNontrivial hβ hEnergy
                (finiteZ2GaugeReplaceCoordinate B source g) f) -
          finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryExpectation
              H β energyIdentity energyNontrivial hβ hEnergy
              (finiteZ2GaugeReplaceCoordinate B source g)
              (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryRandomScan
                H β energyIdentity energyNontrivial hβ hEnergy
                (finiteZ2GaugeReplaceCoordinate B source g) f)| := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryExpectation
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryRandomScan
  apply P.globalExpectation_crossWeight_le_oneStep
  · intro X
    exact
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_pos
        H β energyIdentity energyNontrivial hβ hEnergy B X
  · intro X
    exact
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_pos
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteZ2GaugeReplaceCoordinate B source g) X
  · exact finiteEvenFourTorusZ2AugmentedCoordinate_card_pos H
  · intro target
    exact
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy source target
  · intro X target
    exact
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryConditionalCrossL1_le_sourceBound
        H β energyIdentity energyNontrivial hβ hEnergy source g B X target

/-- Exact three-coordinate source contribution in the stationary comparison. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryThreeCoordinateError
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (source : FiniteEvenFourTorusSpatialLink H)
    (variation : FiniteEvenFourTorusZ2AugmentedCoordinate H → ℝ) : ℝ :=
  (Fintype.card (FiniteEvenFourTorusZ2AugmentedCoordinate H) : ℝ)⁻¹ *
    (2 * (1 - Real.exp
      (-2 * β * (energyNontrivial - energyIdentity))) *
      ∑ target ∈
        finiteEvenFourTorusZ2AugmentedBoundarySourceSupport H source,
          variation target)

/-- Residual expectation discrepancy after one random-scan step for the right
boundary weight. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryRandomScanResidual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B B' : FiniteEvenFourTorusZ2SliceConfiguration H)
    (f : FiniteEvenFourTorusZ2AugmentedConfiguration H → ℝ) : ℝ :=
  |finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryExpectation
        H β energyIdentity energyNontrivial hβ hEnergy B
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryRandomScan
          H β energyIdentity energyNontrivial hβ hEnergy B' f) -
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryExpectation
        H β energyIdentity energyNontrivial hβ hEnergy B'
        (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryRandomScan
          H β energyIdentity energyNontrivial hβ hEnergy B' f)|

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
    |finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryExpectation
          H β energyIdentity energyNontrivial hβ hEnergy B f -
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryExpectation
          H β energyIdentity energyNontrivial hβ hEnergy
          (finiteZ2GaugeReplaceCoordinate B source g) f| ≤
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryThreeCoordinateError
          H β energyIdentity energyNontrivial source P.variation +
        finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryRandomScanResidual
          H β energyIdentity energyNontrivial hβ hEnergy B
          (finiteZ2GaugeReplaceCoordinate B source g) f := by
  unfold
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryThreeCoordinateError
    finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryRandomScanResidual
  rw [←
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound_pairing_eq
      H β energyIdentity energyNontrivial source P.variation]
  exact
    P.finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryExpectation_difference_abs_le_sourcePairing_add_randomScanResidual
      H β energyIdentity energyNontrivial hβ hEnergy source g B

end

end MathlibAnalytic
end MGAP4D
