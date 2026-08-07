import MGAP4D.MathlibAnalytic.FiniteBoltzmannWeightedSecondVariation
import MGAP4D.MathlibAnalytic.FiniteUniformAverageComplementKernelCongruence
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGroundLiftedFirstVariationCancellation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Named derivative profile of the proof-free analytic finite Z₂ one-slab
kernel at arbitrary beta. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteBoltzmannWeightedProfileFirstVariationProfile
    ((Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹)
    (fun U : FiniteEvenFourTorusZ2TemporalLinkField H =>
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
        H 0 energyIdentity energyNontrivial U A B)
    (fun _ => 1)
    β

/-- Exact non-factorial beta-zero second variation of the finite Z₂ one-slab
kernel: the uniform temporal-link second moment of the complete slab action. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
    ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
        H 0 energyIdentity energyNontrivial U A B) ^ 2

/-- The named first-variation profile is the actual derivative of the analytic
finite Z₂ one-slab kernel at every real beta. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_hasDerivAt_named
    (H : ℕ)
    (energyIdentity energyNontrivial β : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    HasDerivAt
      (fun t : ℝ =>
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic
          H energyIdentity energyNontrivial t A B)
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile
        H energyIdentity energyNontrivial β A B)
      β := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile
  exact
    finiteBoltzmannWeightedProfile_hasDerivAt
      ((Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹)
      (fun U : FiniteEvenFourTorusZ2TemporalLinkField H =>
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
          H 0 energyIdentity energyNontrivial U A B)
      (fun _ => 1)
      β

/-- The derivative of the named first-variation profile at beta zero is exactly
the named second slab-action moment. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile_hasDerivAt_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    HasDerivAt
      (fun β : ℝ =>
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile
          H energyIdentity energyNontrivial β A B)
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
        H energyIdentity energyNontrivial A B)
      0 := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
    finiteBoltzmannWeightedProfileSecondVariation
    finiteBoltzmannWeightedSumSecondVariation
  simpa using
    (finiteBoltzmannWeightedProfileFirstVariationProfile_hasDerivAt_zero
      ((Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹)
      (fun U : FiniteEvenFourTorusZ2TemporalLinkField H =>
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
          H 0 energyIdentity energyNontrivial U A B)
      (fun _ => (1 : ℝ)))

/-- At beta zero the named all-beta first-variation profile agrees with Package
P's existing beta-zero first-variation coefficient. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile
        H energyIdentity energyNontrivial 0 A B =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
        H energyIdentity energyNontrivial A B := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariationProfile
    finiteBoltzmannWeightedProfileFirstVariationProfile
    finiteBoltzmannWeightedSumFirstVariationProfile
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
  simp only [mul_zero, Real.exp_zero, mul_one]

/-- Proof-free second-order product-rule model for a scalar-normalized kernel.
If `ν₀,ν₁,ν₂` are respectively the value, first derivative, and second
derivative of a scalar normalization at beta zero, then the second derivative
of `ν(β) K(β)` has exactly this form. -/
noncomputable def finiteEvenFourTorusZ2NormalizedOneSlabKernelSecondVariationModel
    (H : ℕ)
    (energyIdentity energyNontrivial ν₀ ν₁ ν₂ : ℝ)
    (B A : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  ν₀ *
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
        H energyIdentity energyNontrivial B A +
    (2 * ν₁) *
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
        H energyIdentity energyNontrivial B A +
    ν₂

/-- After subtracting the `ν₀`-scaled raw second moment, all remaining
normalization-derivative terms are boundary-additive. -/
theorem finiteEvenFourTorusZ2NormalizedOneSlabKernelSecondVariationModel_sub_scaledRaw_sub_right_independent
    (H : ℕ)
    (energyIdentity energyNontrivial ν₀ ν₁ ν₂ : ℝ)
    (B B' A A' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (finiteEvenFourTorusZ2NormalizedOneSlabKernelSecondVariationModel
          H energyIdentity energyNontrivial ν₀ ν₁ ν₂ B A -
        ν₀ * finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
          H energyIdentity energyNontrivial B A) -
      (finiteEvenFourTorusZ2NormalizedOneSlabKernelSecondVariationModel
          H energyIdentity energyNontrivial ν₀ ν₁ ν₂ B A' -
        ν₀ * finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
          H energyIdentity energyNontrivial B A') =
    (finiteEvenFourTorusZ2NormalizedOneSlabKernelSecondVariationModel
          H energyIdentity energyNontrivial ν₀ ν₁ ν₂ B' A -
        ν₀ * finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
          H energyIdentity energyNontrivial B' A) -
      (finiteEvenFourTorusZ2NormalizedOneSlabKernelSecondVariationModel
          H energyIdentity energyNontrivial ν₀ ν₁ ν₂ B' A' -
        ν₀ * finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
          H energyIdentity energyNontrivial B' A') := by
  unfold finiteEvenFourTorusZ2NormalizedOneSlabKernelSecondVariationModel
  have h :=
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation_sub_right_independent
      H energyIdentity energyNontrivial B B' A A'
  linear_combination (2 * ν₁) * h

/-- Double centering removes every first/second derivative of the scalar
normalization.  The normalized second-order QQ block depends only on `ν₀` times
the raw slab-action second moment. -/
theorem finiteEvenFourTorusZ2NormalizedOneSlabKernelSecondVariationModel_doubleCentered_eq_scaledRaw
    (H : ℕ)
    (energyIdentity energyNontrivial ν₀ ν₁ ν₂ : ℝ) :
    finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (finiteEvenFourTorusZ2NormalizedOneSlabKernelSecondVariationModel
            H energyIdentity energyNontrivial ν₀ ν₁ ν₂)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) =
      finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (fun B A : FiniteEvenFourTorusZ2SliceConfiguration H =>
            ν₀ * finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
              H energyIdentity energyNontrivial B A)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) := by
  exact
    finiteUniformAverageComplement_comp_finiteKernelOperator_congr_of_sub_right_independent
      (finiteEvenFourTorusZ2NormalizedOneSlabKernelSecondVariationModel
        H energyIdentity energyNontrivial ν₀ ν₁ ν₂)
      (fun B A : FiniteEvenFourTorusZ2SliceConfiguration H =>
        ν₀ * finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
          H energyIdentity energyNontrivial B A)
      (finiteEvenFourTorusZ2NormalizedOneSlabKernelSecondVariationModel_sub_scaledRaw_sub_right_independent
        H energyIdentity energyNontrivial ν₀ ν₁ ν₂)

/-- Audit-visible Package-V second-moment receipt. -/
structure Z2FiniteEvenFourTorusOneSlabKernelSecondVariationPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ) where
  secondVariation :
    FiniteEvenFourTorusZ2SliceConfiguration H →
      FiniteEvenFourTorusZ2SliceConfiguration H → ℝ
  secondVariation_eq :
    secondVariation =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
        H energyIdentity energyNontrivial
  normalizationDerivativeCancellation :
    ∀ ν₀ ν₁ ν₂ : ℝ,
      finiteUniformAverageComplementLinearMap.comp
          ((finiteKernelOperator
            (finiteEvenFourTorusZ2NormalizedOneSlabKernelSecondVariationModel
              H energyIdentity energyNontrivial ν₀ ν₁ ν₂)).toLinearMap.comp
            finiteUniformAverageComplementLinearMap) =
        finiteUniformAverageComplementLinearMap.comp
          ((finiteKernelOperator
            (fun B A : FiniteEvenFourTorusZ2SliceConfiguration H =>
              ν₀ * finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
                H energyIdentity energyNontrivial B A)).toLinearMap.comp
            finiteUniformAverageComplementLinearMap)

/-- Construct the Package-V second-moment receipt. -/
noncomputable def z2FiniteEvenFourTorusOneSlabKernelSecondVariationPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ) :
    Z2FiniteEvenFourTorusOneSlabKernelSecondVariationPackage
      H energyIdentity energyNontrivial where
  secondVariation :=
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
      H energyIdentity energyNontrivial
  secondVariation_eq := rfl
  normalizationDerivativeCancellation := fun ν₀ ν₁ ν₂ =>
    finiteEvenFourTorusZ2NormalizedOneSlabKernelSecondVariationModel_doubleCentered_eq_scaledRaw
      H energyIdentity energyNontrivial ν₀ ν₁ ν₂

end

end MathlibAnalytic
end MGAP4D
