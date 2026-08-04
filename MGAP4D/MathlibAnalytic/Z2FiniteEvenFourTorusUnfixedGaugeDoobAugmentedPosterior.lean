import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobPosteriorLocalControl
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Unnormalized augmented one-slab posterior weight on a temporal-link field
and a lower boundary slice, at fixed upper boundary.  Its temporal-link
marginal is the raw one-slab kernel times the positive Perron ground. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
      Real.exp (-β *
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
          H β energyIdentity energyNontrivial U A B) *
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
      H β energyIdentity energyNontrivial hβ hEnergy A

/-- The augmented unnormalized weight is nonnegative. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 ≤ finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight
      H β energyIdentity energyNontrivial hβ hEnergy U A B := by
  have hp :
      0 ≤ finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H β energyIdentity energyNontrivial hβ hEnergy A :=
    le_of_lt
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_pos
        H β energyIdentity energyNontrivial hβ hEnergy A)
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight
  positivity

/-- Summing the augmented weight over temporal links recovers exactly the raw
one-slab kernel multiplied by the Perron ground. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight_sum_temporal
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight
        H β energyIdentity energyNontrivial hβ hEnergy U A B) =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
          H β energyIdentity energyNontrivial hβ hEnergy A B *
        finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β energyIdentity energyNontrivial hβ hEnergy A := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight
  rw [← Finset.sum_mul]
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_apply]
  rw [← Finset.mul_sum]

/-- Column normalizer of the actual Perron posterior. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  ∑ A : FiniteEvenFourTorusZ2SliceConfiguration H,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy A B *
      finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
        H β energyIdentity energyNontrivial hβ hEnergy A

/-- The actual posterior normalizer is strictly positive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer
      H β energyIdentity energyNontrivial hβ hEnergy B := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer
  apply Finset.sum_pos
  · intro A _hA
    exact mul_pos
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_pos
        H β energyIdentity energyNontrivial hβ hEnergy A B)
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_pos
        H β energyIdentity energyNontrivial hβ hEnergy A)
  · exact ⟨1, Finset.mem_univ _⟩

/-- Normalized augmented Gibbs posterior on `(temporal links, lower slice)` at
fixed upper boundary. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight
      H β energyIdentity energyNontrivial hβ hEnergy U A B /
    finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer
      H β energyIdentity energyNontrivial hβ hEnergy B

/-- The normalized augmented posterior is nonnegative. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 ≤ finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
      H β energyIdentity energyNontrivial hβ hEnergy U A B := by
  exact div_nonneg
    (finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight_nonneg
      H β energyIdentity energyNontrivial hβ hEnergy U A B)
    (le_of_lt
      (finiteEvenFourTorusZ2UnfixedGaugeDoobPosteriorNormalizer_pos
        H β energyIdentity energyNontrivial hβ hEnergy B))

/-- The lower-slice marginal of the augmented posterior is exactly the actual
Perron-ground Doob transition kernel. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior_sum_temporal
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
        H β energyIdentity energyNontrivial hβ hEnergy U A B) =
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
        H β energyIdentity energyNontrivial hβ hEnergy A B := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
  rw [Finset.sum_div]
  rw [finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedWeight_sum_temporal]
  exact
    (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel_eq_posterior
      H β energyIdentity energyNontrivial hβ hEnergy A B).symm

/-- The augmented posterior has total mass one for every fixed upper boundary. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior_sum_eq_one
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (∑ A : FiniteEvenFourTorusZ2SliceConfiguration H,
      ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
        finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
          H β energyIdentity energyNontrivial hβ hEnergy U A B) = 1 := by
  calc
    (∑ A : FiniteEvenFourTorusZ2SliceConfiguration H,
      ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
        finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
          H β energyIdentity energyNontrivial hβ hEnergy U A B) =
        ∑ A : FiniteEvenFourTorusZ2SliceConfiguration H,
          finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
            H β energyIdentity energyNontrivial hβ hEnergy A B := by
      apply Finset.sum_congr rfl
      intro A _hA
      exact
        finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior_sum_temporal
          H β energyIdentity energyNontrivial hβ hEnergy A B
    _ = 1 :=
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel_sum_eq_one
        H β energyIdentity energyNontrivial hβ hEnergy B

end

end MathlibAnalytic
end MGAP4D
