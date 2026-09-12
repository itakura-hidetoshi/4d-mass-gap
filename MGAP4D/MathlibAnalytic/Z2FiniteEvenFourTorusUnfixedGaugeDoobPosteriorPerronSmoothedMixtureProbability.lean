import MGAP4D.MathlibAnalytic.FinitePositiveWeightMixtureProbability
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorActualParallelCoupling
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobPosteriorPerronSmoothedMixture
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Residual-gauge mixture scale attached to one transformed upper-slice
environment. -/
def finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureScale
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) : ℝ :=
  finiteEvenFourTorusZ2TemporalGaugePosteriorScale
    H β energyIdentity energyNontrivial (g • environment)

/-- Perron-smoothed posterior component indexed by one residual-gauge
transformation of the upper-slice environment. -/
def finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureWeight
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (hidden : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
    H β energyIdentity energyNontrivial hβ hEnergy
    (g • environment) hidden

/-- Every residual-gauge mixture scale is strictly positive. -/
theorem finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureScale_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) :
    0 < finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureScale
      H β energyIdentity energyNontrivial environment g := by
  exact finiteEvenFourTorusZ2TemporalGaugePosteriorScale_pos
    H β energyIdentity energyNontrivial (g • environment)

/-- Every residual-gauge Perron-smoothed component weight is strictly positive
throughout the actual high-temperature continuation interval. -/
theorem finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureWeight_pos
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureWeight
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
      environment g hidden := by
  exact C.posteriorWeight_pos
    β hβ hβCutoff H (g • environment) hidden

/-- Probability law of the latent residual-gauge mixture index. -/
noncomputable def
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FiniteRealProbabilityData
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) :=
  finitePositiveWeightMixtureIndexProbabilityData
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureScale
      H β energyIdentity energyNontrivial environment)
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureWeight
      H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureScale_pos
      H β energyIdentity energyNontrivial environment)
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureWeight_pos
      C β hβ hβCutoff H environment)

/-- Normalized probability law of one residual-gauge Perron-smoothed
posterior component. -/
noncomputable def
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) :
    FiniteRealProbabilityData
      (FiniteEvenFourTorusZ2SliceConfiguration H) :=
  finitePositiveWeightMixtureComponentProbabilityData
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureWeight
      H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureWeight_pos
      C β hβ hβCutoff H environment)
    g

/-- Probability law obtained by normalizing the residual-gauge mixture of
Perron-smoothed posterior components. -/
noncomputable def
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureProbabilityData
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FiniteRealProbabilityData
      (FiniteEvenFourTorusZ2SliceConfiguration H) :=
  finitePositiveWeightMixtureProbabilityData
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureScale
      H β energyIdentity energyNontrivial environment)
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureWeight
      H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureScale_pos
      H β energyIdentity energyNontrivial environment)
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureWeight_pos
      C β hβ hβCutoff H environment)

/-- Normalizing the actual residual-gauge averaged ground posterior gives the
same probability law as normalizing the raw positive mixture of the
Perron-smoothed posterior components.  The common residual-group cardinality
factor cancels exactly and no random-scan/geometric gap identification is used. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugeGroundPosteriorProbability_eq_residualGaugePerronSmoothedMixture
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (finiteEvenFourTorusZ2UnfixedGaugeGroundPosteriorProbabilityData
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
      environment).probability hidden =
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureProbabilityData
        C β hβ hβCutoff H environment).probability hidden := by
  let scale :=
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureScale
      H β energyIdentity energyNontrivial environment
  let weight :=
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureWeight
      H β energyIdentity energyNontrivial hβ.le hEnergy.le environment
  have hscale : ∀ g, 0 < scale g := by
    intro g
    exact finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureScale_pos
      H β energyIdentity energyNontrivial environment g
  have hweight : ∀ g hidden, 0 < weight g hidden := by
    intro g z
    exact finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureWeight_pos
      C β hβ hβCutoff H environment g z
  have hRawPartition :
      0 < finiteRealWeightPartition
        (finitePositiveWeightMixtureRaw scale weight) :=
    finiteRealWeightPartition_pos_of_pos
      (finitePositiveWeightMixtureRaw scale weight)
      (finitePositiveWeightMixtureRaw_pos scale weight hscale hweight)
  have hCardInv :
      (Fintype.card
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) : ℝ)⁻¹ ≠ 0 := by
    positivity
  have hPoint
      (z : FiniteEvenFourTorusZ2SliceConfiguration H) :
      finiteEvenFourTorusZ2UnfixedGaugeGroundPosteriorWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le
          environment z =
        (Fintype.card
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) : ℝ)⁻¹ *
          finitePositiveWeightMixtureRaw scale weight z := by
    simpa [scale, weight, finitePositiveWeightMixtureRaw,
      finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureScale,
      finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureWeight] using
      finiteEvenFourTorusZ2UnfixedGaugeGroundPosteriorWeight_eq_perronSmoothedMixture
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
        environment z
  have hPartition :
      finiteRealWeightPartition
          (finiteEvenFourTorusZ2UnfixedGaugeGroundPosteriorWeight
            H β energyIdentity energyNontrivial hβ.le hEnergy.le
            environment) =
        (Fintype.card
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) : ℝ)⁻¹ *
          finiteRealWeightPartition
            (finitePositiveWeightMixtureRaw scale weight) := by
    unfold finiteRealWeightPartition
    calc
      (∑ z : FiniteEvenFourTorusZ2SliceConfiguration H,
        finiteEvenFourTorusZ2UnfixedGaugeGroundPosteriorWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le
          environment z) =
          ∑ z : FiniteEvenFourTorusZ2SliceConfiguration H,
            (Fintype.card
              (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) : ℝ)⁻¹ *
              finitePositiveWeightMixtureRaw scale weight z := by
        apply Finset.sum_congr rfl
        intro z _hz
        exact hPoint z
      _ =
          (Fintype.card
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) : ℝ)⁻¹ *
            ∑ z : FiniteEvenFourTorusZ2SliceConfiguration H,
              finitePositiveWeightMixtureRaw scale weight z := by
        rw [Finset.mul_sum]
  change
    finiteRealWeightProbability
        (finiteEvenFourTorusZ2UnfixedGaugeGroundPosteriorWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
        hidden =
      finiteRealWeightProbability
        (finitePositiveWeightMixtureRaw scale weight) hidden
  unfold finiteRealWeightProbability
  rw [hPoint hidden, hPartition]
  field_simp [hCardInv, ne_of_gt hRawPartition]

/-- The actual geometric one-slab Doob row is a finite convex mixture of the
normalized Perron-smoothed posterior components, with latent residual-gauge
weights proportional to `temporalScale × componentPartition`. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel_eq_residualGaugePerronSmoothedMixture
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
        hidden environment =
      ∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
          C β hβ hβCutoff H environment).probability g *
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
          C β hβ hβCutoff H environment g).probability hidden := by
  calc
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
        hidden environment =
      (finiteEvenFourTorusZ2UnfixedGaugeGroundPosteriorProbabilityData
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
        environment).probability hidden := by
      symm
      exact
        finiteEvenFourTorusZ2UnfixedGaugeGroundPosteriorProbability_eq_doobKernel
          H β energyIdentity energyNontrivial hβ.le hEnergy.le
          environment hidden
    _ =
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureProbabilityData
        C β hβ hβCutoff H environment).probability hidden :=
      finiteEvenFourTorusZ2UnfixedGaugeGroundPosteriorProbability_eq_residualGaugePerronSmoothedMixture
        C β hβ hβCutoff H environment hidden
    _ =
      ∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
          C β hβ hβCutoff H environment).probability g *
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
          C β hβ hβCutoff H environment g).probability hidden := by
      exact finitePositiveWeightMixtureProbability_eq_sum
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureScale
          H β energyIdentity energyNontrivial environment)
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureScale_pos
          H β energyIdentity energyNontrivial environment)
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureWeight_pos
          C β hβ hβCutoff H environment)
        hidden

end

end MathlibAnalytic
end MGAP4D
