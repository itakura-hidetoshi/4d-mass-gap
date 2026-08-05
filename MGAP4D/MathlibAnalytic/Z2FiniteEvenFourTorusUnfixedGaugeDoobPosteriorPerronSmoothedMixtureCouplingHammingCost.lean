import MGAP4D.MathlibAnalytic.FinitePositiveWeightConditionalL1Telescoping
import MGAP4D.MathlibAnalytic.FiniteRealProbabilityMixtureCouplingCost
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobPosteriorPerronSmoothedMixtureCoupling
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Expected Hamming cost of one pair of residual-gauge Perron-smoothed
posterior component couplings. -/
noncomputable def
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedHamming
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (g h : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) : ℝ :=
  (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentCouplingData
    C β hβ hβCutoff H left right g h).expectedCost
      finiteProductHammingDistanceReal

/-- Expected Hamming cost of the exact-marginal actual geometric Doob mixture
coupling. -/
noncomputable def
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedHamming
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureCouplingData
    C β hβ hβCutoff H left right).expectedCost
      finiteProductHammingDistanceReal

/-- The actual geometric Doob mixture expected Hamming cost is exactly the
latent residual-gauge coupling average of the component expected Hamming
costs. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedHamming_eq
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
      ∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        ∑ h : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
          (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
            C β hβ hβCutoff H left right).joint g h *
          finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedHamming
            C β hβ hβCutoff H left right g h := by
  unfold
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedHamming
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedHamming
  change
    (finiteRealProbabilityMixtureCouplingData
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
        C β hβ hβCutoff H left right)
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentCouplingData
        C β hβ hβCutoff H left right)).expectedCost
          finiteProductHammingDistanceReal = _
  exact finiteRealProbabilityMixtureCoupling_expectedCost_eq
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
      C β hβ hβCutoff H left right)
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentCouplingData
      C β hβ hβCutoff H left right)
    finiteProductHammingDistanceReal

/-- Any pairwise component Hamming-cost bounds pass to the actual geometric
Doob mixture coupling with the exact latent residual-gauge coupling weights. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedHamming_le
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (bound :
      FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H →
      FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H → ℝ)
    (hBound :
      ∀ g h : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedHamming
            C β hβ hβCutoff H left right g h ≤ bound g h) :
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedHamming
        C β hβ hβCutoff H left right ≤
      ∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        ∑ h : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
          (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
            C β hβ hβCutoff H left right).joint g h * bound g h := by
  unfold
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureExpectedHamming
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectedHamming
      at hBound ⊢
  change
    (finiteRealProbabilityMixtureCouplingData
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
        C β hβ hβCutoff H left right)
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentCouplingData
        C β hβ hβCutoff H left right)).expectedCost
          finiteProductHammingDistanceReal ≤ _
  exact finiteRealProbabilityMixtureCoupling_expectedCost_le
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
      C β hβ hβCutoff H left right)
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentCouplingData
      C β hβ hβCutoff H left right)
    finiteProductHammingDistanceReal
    bound
    hBound

end

end MathlibAnalytic
end MGAP4D
