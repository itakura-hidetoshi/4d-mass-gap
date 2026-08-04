import MGAP4D.MathlibAnalytic.FinitePositiveWeightCrossWeightRandomScanComparison
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedLocalTiltConditionalSource
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The pairing of the explicit actual source vector with an arbitrary
variation profile is exactly supported on the three boundary-source
coordinates. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound_pairing_eq
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (source : FiniteEvenFourTorusSpatialLink H)
    (variation : FiniteEvenFourTorusZ2AugmentedCoordinate H → ℝ) :
    (∑ target : FiniteEvenFourTorusZ2AugmentedCoordinate H,
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound
          H β energyIdentity energyNontrivial source target *
        variation target) =
      2 *
          (1 - Real.exp
            (-2 * β * (energyNontrivial - energyIdentity))) *
        ∑ target in
          finiteEvenFourTorusZ2AugmentedBoundarySourceSupport H source,
            variation target := by
  classical
  unfold
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound
  calc
    (∑ target : FiniteEvenFourTorusZ2AugmentedCoordinate H,
      (if target ∈
          finiteEvenFourTorusZ2AugmentedBoundarySourceSupport H source then
        2 *
          (1 - Real.exp
            (-2 * β * (energyNontrivial - energyIdentity)))
      else 0) * variation target) =
      ∑ target : FiniteEvenFourTorusZ2AugmentedCoordinate H,
        if target ∈
            finiteEvenFourTorusZ2AugmentedBoundarySourceSupport H source then
          2 *
              (1 - Real.exp
                (-2 * β * (energyNontrivial - energyIdentity))) *
            variation target
        else 0 := by
      apply Finset.sum_congr rfl
      intro target _htarget
      by_cases hmem :
          target ∈
            finiteEvenFourTorusZ2AugmentedBoundarySourceSupport H source
      · simp [hmem]
      · simp [hmem]
    _ = ∑ target in
        finiteEvenFourTorusZ2AugmentedBoundarySourceSupport H source,
          2 *
              (1 - Real.exp
                (-2 * β * (energyNontrivial - energyIdentity))) *
            variation target := by
      rw [← Finset.sum_filter]
      simp
    _ = 2 *
          (1 - Real.exp
            (-2 * β * (energyNontrivial - energyIdentity))) *
        ∑ target in
          finiteEvenFourTorusZ2AugmentedBoundarySourceSupport H source,
            variation target := by
      rw [Finset.mul_sum]

/-- Actual cross-boundary random-scan comparison on the encoded augmented
state.  This is an auxiliary comparison statement for the internal Gibbs
specification and is not identified with the geometric one-slab Doob
transition. -/
theorem FiniteProductVariationBound.finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryRandomScan_difference_abs_le_sourcePairing
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    {f : FiniteEvenFourTorusZ2AugmentedConfiguration H → ℝ}
    (P : FiniteProductVariationBound f)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) :
    |finitePositiveWeightRandomScanConditionalExpectation
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
            H β energyIdentity energyNontrivial hβ hEnergy B)
          f X -
        finitePositiveWeightRandomScanConditionalExpectation
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
            H β energyIdentity energyNontrivial hβ hEnergy
            (finiteZ2GaugeReplaceCoordinate B source g))
          f X| ≤
      (Fintype.card
          (FiniteEvenFourTorusZ2AugmentedCoordinate H) : ℝ)⁻¹ *
        ∑ target : FiniteEvenFourTorusZ2AugmentedCoordinate H,
          finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound
              H β energyIdentity energyNontrivial source target *
            P.variation target := by
  apply P.randomScan_crossWeight_difference_abs_le_sourcePairing
  · intro Y
    exact
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_pos
        H β energyIdentity energyNontrivial hβ hEnergy B Y
  · intro Y
    exact
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight_pos
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteZ2GaugeReplaceCoordinate B source g) Y
  · intro Y target
    exact
      finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedBoundaryConditionalCrossL1_le_sourceBound
        H β energyIdentity energyNontrivial hβ hEnergy source g B Y target

/-- Exact three-coordinate form of the actual auxiliary random-scan comparison
error. -/
theorem FiniteProductVariationBound.finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryRandomScan_difference_abs_le_threeCoordinatePairing
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    {f : FiniteEvenFourTorusZ2AugmentedConfiguration H → ℝ}
    (P : FiniteProductVariationBound f)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (X : FiniteEvenFourTorusZ2AugmentedConfiguration H) :
    |finitePositiveWeightRandomScanConditionalExpectation
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
            H β energyIdentity energyNontrivial hβ hEnergy B)
          f X -
        finitePositiveWeightRandomScanConditionalExpectation
          (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
            H β energyIdentity energyNontrivial hβ hEnergy
            (finiteZ2GaugeReplaceCoordinate B source g))
          f X| ≤
      (Fintype.card
          (FiniteEvenFourTorusZ2AugmentedCoordinate H) : ℝ)⁻¹ *
        (2 *
            (1 - Real.exp
              (-2 * β * (energyNontrivial - energyIdentity))) *
          ∑ target in
            finiteEvenFourTorusZ2AugmentedBoundarySourceSupport H source,
              P.variation target) := by
  rw [←
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound_pairing_eq
      H β energyIdentity energyNontrivial source P.variation]
  exact
    P.finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryRandomScan_difference_abs_le_sourcePairing
      H β energyIdentity energyNontrivial hβ hEnergy source g B X

end

end MathlibAnalytic
end MGAP4D
