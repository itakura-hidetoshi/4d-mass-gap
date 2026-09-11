import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeGroundStateDoobPosteriorProbability
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCanonicalPerronSmoothedPosteriorInfluenceContinuity
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Temporal-gauge raw posterior built from the repository's chosen positive
unfixed-gauge Perron ground. -/
def finiteEvenFourTorusZ2TemporalGaugeChosenGroundRawPosteriorWeight
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel
      hidden environment *
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
      H β energyIdentity energyNontrivial hβ hEnergy hidden

/-- The environment-dependent positive scalar relating a temporal-gauge raw
posterior to the chosen-ground Perron-smoothed posterior. -/
def finiteEvenFourTorusZ2TemporalGaugePosteriorScale
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2TemporalCrossingScale
      H β energyIdentity energyNontrivial *
    finiteEvenFourTorusZ2SpatialHalfWeight
      H β energyIdentity energyNontrivial environment

/-- The temporal-gauge posterior scale is strictly positive. -/
theorem finiteEvenFourTorusZ2TemporalGaugePosteriorScale_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2TemporalGaugePosteriorScale
      H β energyIdentity energyNontrivial environment := by
  unfold finiteEvenFourTorusZ2TemporalGaugePosteriorScale
  exact mul_pos
    (finiteEvenFourTorusZ2TemporalCrossingScale_pos
      H β energyIdentity energyNontrivial)
    (finiteEvenFourTorusZ2SpatialHalfWeight_pos
      H β energyIdentity energyNontrivial environment)

/-- Exact positive scalar relation for the chosen-ground temporal posterior. -/
theorem finiteEvenFourTorusZ2TemporalGaugeChosenGroundRawPosteriorWeight_eq_scale_mul
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2TemporalGaugeChosenGroundRawPosteriorWeight
        H β energyIdentity energyNontrivial hβ hEnergy environment hidden =
      finiteEvenFourTorusZ2TemporalGaugePosteriorScale
          H β energyIdentity energyNontrivial environment *
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H β energyIdentity energyNontrivial hβ hEnergy
          environment hidden := by
  unfold finiteEvenFourTorusZ2TemporalGaugeChosenGroundRawPosteriorWeight
    finiteEvenFourTorusZ2TemporalGaugePosteriorScale
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedHiddenWeight
    finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
  rw [finite_os_gram_kernel_sandwich_apply]
  rw [finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel_eq_scale_mul_normalized
    H β energyIdentity energyNontrivial hβ hEnergy hidden environment]
  ring

/-- The temporal raw posterior used in the residual-gauge average is exactly
the chosen-ground raw posterior above. -/
theorem finiteEvenFourTorusZ2TemporalGaugeGroundPosteriorWeight_eq_chosen
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2TemporalGaugeGroundPosteriorWeight
        H β energyIdentity energyNontrivial hβ hEnergy environment hidden =
      finiteEvenFourTorusZ2TemporalGaugeChosenGroundRawPosteriorWeight
        H β energyIdentity energyNontrivial hβ hEnergy environment hidden := by
  rfl

/-- Exact mixture bridge: the unnormalized geometric unfixed-gauge Doob
posterior is the residual-gauge average of positive scalar multiples of the
actual Perron-smoothed posterior laws. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeGroundPosteriorWeight_eq_perronSmoothedMixture
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeGroundPosteriorWeight
        H β energyIdentity energyNontrivial hβ hEnergy environment hidden =
      (Fintype.card
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) : ℝ)⁻¹ *
        ∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
          finiteEvenFourTorusZ2TemporalGaugePosteriorScale
              H β energyIdentity energyNontrivial (g • environment) *
            finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
              H β energyIdentity energyNontrivial hβ hEnergy
              (g • environment) hidden := by
  rw [
    finiteEvenFourTorusZ2UnfixedGaugeGroundPosteriorWeight_eq_residualGaugeAverage]
  congr 1
  apply Finset.sum_congr rfl
  intro g _hg
  rw [finiteEvenFourTorusZ2TemporalGaugeGroundPosteriorWeight_eq_chosen]
  exact
    finiteEvenFourTorusZ2TemporalGaugeChosenGroundRawPosteriorWeight_eq_scale_mul
      H β energyIdentity energyNontrivial hβ hEnergy
      (g • environment) hidden

end

end MathlibAnalytic
end MGAP4D
