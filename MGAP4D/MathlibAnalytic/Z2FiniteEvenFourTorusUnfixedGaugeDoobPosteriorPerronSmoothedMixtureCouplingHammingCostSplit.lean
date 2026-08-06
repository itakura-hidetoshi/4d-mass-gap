import MGAP4D.MathlibAnalytic.FiniteRealProbabilityMixtureCouplingCostSplit
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobPosteriorPerronSmoothedMixtureCouplingHammingCost
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The overlap coupling of the two actual residual-gauge latent laws has
exact disagreement mass equal to half their unhalved `L¹` distance. -/
theorem
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCoupling_disagreementMass_eq_half_mul_l1Distance
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
      C β hβ hβCutoff H left right).disagreementMass =
      (2 : ℝ)⁻¹ *
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
          C β hβ hβCutoff H left).l1Distance
          (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
            C β hβ hβCutoff H right) := by
  unfold
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
  exact
    FiniteRealProbabilityData.overlapCouplingData_disagreementMass_eq_half_mul_l1Distance
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
        C β hβ hβCutoff H left)
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
        C β hβ hβCutoff H right)

/-- Same-residual-gauge-index contribution to the actual geometric Doob
mixture expected Hamming cost. -/
noncomputable def
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureDiagonalExpectedHamming
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteRealProbabilityMixtureCouplingDiagonalExpectedCost
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
      C β hβ hβCutoff H left right)
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentCouplingData
      C β hβ hβCutoff H left right)
    finiteProductHammingDistanceReal

/-- Different-residual-gauge-index contribution to the actual geometric Doob
mixture expected Hamming cost. -/
noncomputable def
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureOffDiagonalExpectedHamming
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteRealProbabilityMixtureCouplingOffDiagonalExpectedCost
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
      C β hβ hβCutoff H left right)
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentCouplingData
      C β hβ hβCutoff H left right)
    finiteProductHammingDistanceReal

/-- Exact same-index/different-index decomposition of the actual geometric
Doob mixture expected Hamming cost. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedHamming_eq_diagonal_add_offDiagonal
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedHamming
        C β hβ hβCutoff H left right =
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureDiagonalExpectedHamming
          C β hβ hβCutoff H left right +
        finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureOffDiagonalExpectedHamming
          C β hβ hβCutoff H left right := by
  unfold
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedHamming
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureDiagonalExpectedHamming
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureOffDiagonalExpectedHamming
  change
    (finiteRealProbabilityMixtureCouplingData
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
        C β hβ hβCutoff H left right)
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentCouplingData
        C β hβ hβCutoff H left right)).expectedCost
          finiteProductHammingDistanceReal = _
  exact
    finiteRealProbabilityMixtureCoupling_expectedCost_eq_diagonal_add_offDiagonal
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
        C β hβ hβCutoff H left right)
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentCouplingData
        C β hβ hβCutoff H left right)
      finiteProductHammingDistanceReal

/-- Same-index component bounds and a uniform different-index bound control
the actual Doob mixture cost through the latent residual-gauge disagreement
mass. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedHamming_le_diagonal_add_indexDisagreement
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
    (offDiagonalBound : ℝ)
    (hDiagonal :
      ∀ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedHamming
            C β hβ hβCutoff H left right g g ≤ diagonalBound g)
    (hOffDiagonal :
      ∀ g h : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        g ≠ h →
        finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedHamming
            C β hβ hβCutoff H left right g h ≤ offDiagonalBound) :
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedHamming
        C β hβ hβCutoff H left right ≤
      (∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
          C β hβ hβCutoff H left right).joint g g * diagonalBound g) +
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
          C β hβ hβCutoff H left right).disagreementMass *
            offDiagonalBound := by
  unfold
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedHamming
      at hDiagonal hOffDiagonal
  unfold
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedHamming
  change
    (finiteRealProbabilityMixtureCouplingData
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
        C β hβ hβCutoff H left right)
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentCouplingData
        C β hβ hβCutoff H left right)).expectedCost
          finiteProductHammingDistanceReal ≤ _
  exact
    finiteRealProbabilityMixtureCoupling_expectedCost_le_diagonal_add_disagreement
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
        C β hβ hβCutoff H left right)
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentCouplingData
        C β hβ hβCutoff H left right)
      finiteProductHammingDistanceReal
      diagonalBound
      offDiagonalBound
      hDiagonal
      hOffDiagonal

/-- The preceding bound with the latent disagreement term written exactly as
half the unhalved `L¹` distance between the two residual-gauge index laws. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedHamming_le_diagonal_add_halfIndexL1
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
    (offDiagonalBound : ℝ)
    (hDiagonal :
      ∀ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedHamming
            C β hβ hβCutoff H left right g g ≤ diagonalBound g)
    (hOffDiagonal :
      ∀ g h : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        g ≠ h →
        finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedHamming
            C β hβ hβCutoff H left right g h ≤ offDiagonalBound) :
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedHamming
        C β hβ hβCutoff H left right ≤
      (∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
          C β hβ hβCutoff H left right).joint g g * diagonalBound g) +
        ((2 : ℝ)⁻¹ *
          (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
            C β hβ hβCutoff H left).l1Distance
            (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
              C β hβ hβCutoff H right)) * offDiagonalBound := by
  rw [←
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCoupling_disagreementMass_eq_half_mul_l1Distance
      C β hβ hβCutoff H left right]
  exact
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedHamming_le_diagonal_add_indexDisagreement
      C β hβ hβCutoff H left right
      diagonalBound offDiagonalBound hDiagonal hOffDiagonal

end

end MathlibAnalytic
end MGAP4D
