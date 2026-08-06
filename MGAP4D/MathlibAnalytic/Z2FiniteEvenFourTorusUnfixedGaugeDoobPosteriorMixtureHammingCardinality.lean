import MGAP4D.MathlibAnalytic.FiniteRealProbabilityCouplingHammingCardinality
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobPosteriorPerronSmoothedMixtureCouplingHammingCostSplit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Every residual-gauge Perron-smoothed component coupling has expected
Hamming cost bounded by the total number of spatial links. -/
theorem
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedHamming_le_spatialLinkCard
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (g h : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) :
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedHamming
        C β hβ hβCutoff H left right g h ≤
      (Fintype.card (FiniteEvenFourTorusSpatialLink H) : ℝ) := by
  unfold
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedHamming
  exact
    FiniteRealCouplingData.expectedFiniteProductHamming_le_card
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentCouplingData
        C β hβ hβCutoff H left right g h)

/-- Same-index component bounds and the universal spatial-cardinality bound
for different residual-gauge indices give an explicit actual geometric Doob
mixture Hamming estimate. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedHamming_le_diagonal_add_halfIndexL1_mul_spatialLinkCard
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (diagonalBound :
      FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H → ℝ)
    (hDiagonal :
      ∀ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedHamming
            C β hβ hβCutoff H left right g g ≤ diagonalBound g) :
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedHamming
        C β hβ hβCutoff H left right ≤
      (∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
          C β hβ hβCutoff H left right).joint g g * diagonalBound g) +
        ((2 : ℝ)⁻¹ *
          (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
            C β hβ hβCutoff H left).l1Distance
            (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
              C β hβ hβCutoff H right)) *
          (Fintype.card (FiniteEvenFourTorusSpatialLink H) : ℝ) := by
  exact
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedHamming_le_diagonal_add_halfIndexL1
      C β hβ hβCutoff H left right
      diagonalBound
      (Fintype.card (FiniteEvenFourTorusSpatialLink H) : ℝ)
      hDiagonal
      (fun g h _hNe =>
        finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedHamming_le_spatialLinkCard
          C β hβ hβCutoff H left right g h)

/-- Public actual package for the uniform component bound and the resulting
latent-disagreement decomposition. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureHammingCardinalityPackage
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (∀ g h : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
      finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedHamming
          C β hβ hβCutoff H left right g h ≤
        (Fintype.card (FiniteEvenFourTorusSpatialLink H) : ℝ)) ∧
    (∀ diagonalBound :
        FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H → ℝ,
      (∀ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedHamming
            C β hβ hβCutoff H left right g g ≤ diagonalBound g) →
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedHamming
          C β hβ hβCutoff H left right ≤
        (∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
          (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
            C β hβ hβCutoff H left right).joint g g * diagonalBound g) +
          ((2 : ℝ)⁻¹ *
            (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
              C β hβ hβCutoff H left).l1Distance
              (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
                C β hβ hβCutoff H right)) *
            (Fintype.card (FiniteEvenFourTorusSpatialLink H) : ℝ)) := by
  constructor
  · intro g h
    exact
      finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedHamming_le_spatialLinkCard
        C β hβ hβCutoff H left right g h
  · intro diagonalBound hDiagonal
    exact
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedHamming_le_diagonal_add_halfIndexL1_mul_spatialLinkCard
        C β hβ hβCutoff H left right diagonalBound hDiagonal

end

end MathlibAnalytic
end MGAP4D
