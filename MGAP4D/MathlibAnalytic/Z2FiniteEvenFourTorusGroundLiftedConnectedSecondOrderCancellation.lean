import MGAP4D.MathlibAnalytic.FiniteUniformNormalizedAdditiveGroundMixingCancellation
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusOneSlabSecondMomentCrossingReduction
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeBetaZeroNormalizedTransferIntertwining
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Exact absolute beta-zero first variation of the proof-free finite Z₂ one-slab
kernel.  Uniform temporal-link averaging replaces the crossing action by its
boundary-independent mean. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation_eq_additive
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
        H energyIdentity energyNontrivial A B =
      -((1 / 2 : ℝ) *
          finiteEvenFourTorusZ2SpatialWilsonAction
            H energyIdentity energyNontrivial A +
        finiteEvenFourTorusZ2TemporalCrossingMean
          H energyIdentity energyNontrivial +
        (1 / 2 : ℝ) *
          finiteEvenFourTorusZ2SpatialWilsonAction
            H energyIdentity energyNontrivial B) := by
  let n : ℝ := Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H)
  have hn : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) ≠ 0)
  have hcross :=
    finiteEvenFourTorusZ2TemporalLinkAverage_crossingAction_eq_crossingMean
      H energyIdentity energyNontrivial A B
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
  change
    n⁻¹ *
        (∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          -((1 / 2 : ℝ) *
              finiteEvenFourTorusZ2SpatialWilsonAction
                H energyIdentity energyNontrivial A +
            finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
              H 0 energyIdentity energyNontrivial U A B +
            (1 / 2 : ℝ) *
              finiteEvenFourTorusZ2SpatialWilsonAction
                H energyIdentity energyNontrivial B)) = _
  change
    n⁻¹ *
        (∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
            H 0 energyIdentity energyNontrivial U A B) =
      finiteEvenFourTorusZ2TemporalCrossingMean
        H energyIdentity energyNontrivial at hcross
  simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hn] at hcross ⊢
  rw [hcross]
  ring

/-- The exact actual op-norm normalization value at beta zero is the uniform
boundary-cardinality inverse required by the generic Package-W kernel. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar_beta_zero_eq_uniformCardInv
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy =
      (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ :=
  finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar_beta_zero
    H energyIdentity energyNontrivial hEnergy

/-- At the exact beta-zero normalization value, the finite Z₂ normalized
first-variation product-rule model is literally the generic uniform-normalized
additive kernel of Package W.  The normalization derivative remains arbitrary. -/
theorem finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel_eq_uniformNormalizedAdditive
    (H : ℕ)
    (energyIdentity energyNontrivial normalizationDerivative : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel
        H energyIdentity energyNontrivial
        (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹
        normalizationDerivative A B =
      finiteUniformNormalizedAdditiveFirstVariationKernel
        (fun X : FiniteEvenFourTorusZ2SliceConfiguration H =>
          finiteEvenFourTorusZ2SpatialWilsonAction
            H energyIdentity energyNontrivial X)
        (finiteEvenFourTorusZ2TemporalCrossingMean
          H energyIdentity energyNontrivial)
        normalizationDerivative A B := by
  unfold finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel
    finiteUniformNormalizedAdditiveFirstVariationKernel
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation_eq_additive]
  ring

/-- Actual finite-Z₂ specialization of the generic disconnected-mixing
cancellation:

`2 Q T₁ P₀ T₁ Q = Q R_spatial Q`,

where `T₁` is the scalar-normalized beta-zero first-variation product-rule
model at the exact actual normalization value, and
`R_spatial(A,B)=|C_H|⁻¹ (1/2) S(A)S(B)`.

The arbitrary normalization derivative and the temporal crossing mean disappear. -/
theorem finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel_groundMixing_double_eq_spatialRankOne
    (H : ℕ)
    (energyIdentity energyNontrivial normalizationDerivative : ℝ) :
    let T₁ :=
      (finiteKernelOperator
        (finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel
          H energyIdentity energyNontrivial
          (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹
          normalizationDerivative)).toLinearMap
    let P₀ :=
      (finiteUniformAverageProjectorLinearMap :
        FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration H) →ₗ[ℝ]
          FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration H))
    let Q :=
      (finiteUniformAverageComplementLinearMap :
        FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration H) →ₗ[ℝ]
          FiniteBoundaryHilbert (FiniteEvenFourTorusZ2SliceConfiguration H))
    let R :=
      (finiteKernelOperator
        (finiteUniformNormalizedSpatialRankOneKernel
          (fun X : FiniteEvenFourTorusZ2SliceConfiguration H =>
            finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial X))).toLinearMap
    Q.comp (T₁.comp (P₀.comp (T₁.comp Q))) +
        Q.comp (T₁.comp (P₀.comp (T₁.comp Q))) =
      Q.comp (R.comp Q) := by
  let spatial : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ :=
    fun X => finiteEvenFourTorusZ2SpatialWilsonAction
      H energyIdentity energyNontrivial X
  let crossingMean :=
    finiteEvenFourTorusZ2TemporalCrossingMean
      H energyIdentity energyNontrivial
  have hKernel :
      finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel
          H energyIdentity energyNontrivial
          (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹
          normalizationDerivative =
        finiteUniformNormalizedAdditiveFirstVariationKernel
          spatial crossingMean normalizationDerivative := by
    funext A B
    exact
      finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel_eq_uniformNormalizedAdditive
        H energyIdentity energyNontrivial normalizationDerivative A B
  dsimp
  rw [hKernel]
  exact
    finiteUniformNormalizedAdditiveFirstVariation_groundMixing_double_eq_spatialRankOne
      spatial crossingMean normalizationDerivative

/-- Audit-visible actual finite-Z₂ Package-W mixing-cancellation receipt. -/
structure Z2FiniteEvenFourTorusGroundLiftedConnectedSecondOrderCancellationPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ) where
  rawFirstVariationFormula :
    ∀ A B : FiniteEvenFourTorusZ2SliceConfiguration H,
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
          H energyIdentity energyNontrivial A B =
        -((1 / 2 : ℝ) *
            finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial A +
          finiteEvenFourTorusZ2TemporalCrossingMean
            H energyIdentity energyNontrivial +
          (1 / 2 : ℝ) *
            finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial B)
  normalizedModelAgreement :
    ∀ normalizationDerivative : ℝ,
      finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel
          H energyIdentity energyNontrivial
          (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹
          normalizationDerivative =
        finiteUniformNormalizedAdditiveFirstVariationKernel
          (fun X : FiniteEvenFourTorusZ2SliceConfiguration H =>
            finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial X)
          (finiteEvenFourTorusZ2TemporalCrossingMean
            H energyIdentity energyNontrivial)
          normalizationDerivative

/-- Construct the actual finite-Z₂ Package-W mixing-cancellation receipt. -/
noncomputable def z2FiniteEvenFourTorusGroundLiftedConnectedSecondOrderCancellationPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ) :
    Z2FiniteEvenFourTorusGroundLiftedConnectedSecondOrderCancellationPackage
      H energyIdentity energyNontrivial where
  rawFirstVariationFormula := fun A B =>
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation_eq_additive
      H energyIdentity energyNontrivial A B
  normalizedModelAgreement := fun normalizationDerivative => by
    funext A B
    exact
      finiteEvenFourTorusZ2NormalizedOneSlabKernelFirstVariationModel_eq_uniformNormalizedAdditive
        H energyIdentity energyNontrivial normalizationDerivative A B

end

end MathlibAnalytic
end MGAP4D
