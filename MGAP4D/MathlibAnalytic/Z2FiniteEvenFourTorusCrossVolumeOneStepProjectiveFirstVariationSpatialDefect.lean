import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusTemporalLinkCrossingAverage
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeConfigurationKernelNontrivial
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- With the left boundary fixed, the beta-zero kernel first variation changes
only by one half of the spatial Wilson action at the right boundary.  Uniform
temporal-link averaging removes the crossing term exactly. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation_sub_right
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (B A A' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
          H energyIdentity energyNontrivial B A -
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
          H energyIdentity energyNontrivial B A' =
      -(1 / 2 : ℝ) *
        (finiteEvenFourTorusZ2SpatialWilsonAction
            H energyIdentity energyNontrivial A -
          finiteEvenFourTorusZ2SpatialWilsonAction
            H energyIdentity energyNontrivial A') := by
  let n : ℝ := Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H)
  have hn : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) ≠ 0)
  have hcross := finiteEvenFourTorusZ2TemporalLinkAverage_crossingAction_eq
    H 0 energyIdentity energyNontrivial B A B A'
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
  change
    n⁻¹ *
          (∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
            -((1 / 2 : ℝ) *
                finiteEvenFourTorusZ2SpatialWilsonAction
                  H energyIdentity energyNontrivial B +
              finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
                H 0 energyIdentity energyNontrivial U B A +
              (1 / 2 : ℝ) *
                finiteEvenFourTorusZ2SpatialWilsonAction
                  H energyIdentity energyNontrivial A)) -
        n⁻¹ *
          (∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
            -((1 / 2 : ℝ) *
                finiteEvenFourTorusZ2SpatialWilsonAction
                  H energyIdentity energyNontrivial B +
              finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
                H 0 energyIdentity energyNontrivial U B A' +
              (1 / 2 : ℝ) *
                finiteEvenFourTorusZ2SpatialWilsonAction
                  H energyIdentity energyNontrivial A')) = _
  change
    n⁻¹ *
        (∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
            H 0 energyIdentity energyNontrivial U B A) =
      n⁻¹ *
        (∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
            H 0 energyIdentity energyNontrivial U B A') at hcross
  simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hn] at hcross ⊢
  linear_combination hcross

/-- The beta-zero fine fibre first variation changes by kernel multiplicity
and the constant embedding scale times the fine spatial-action defect. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientFirstVariation_sub
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A A' : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientFirstVariation
          H energyIdentity energyNontrivial A b -
      finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientFirstVariation
          H energyIdentity energyNontrivial A' b =
      -(1 / 2 : ℝ) *
        finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H *
        (Fintype.card
          (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker : ℝ) *
        (finiteEvenFourTorusZ2SpatialWilsonAction
            (finiteEvenFourTorusDoubleRefinement H)
            energyIdentity energyNontrivial A -
          finiteEvenFourTorusZ2SpatialWilsonAction
            (finiteEvenFourTorusDoubleRefinement H)
            energyIdentity energyNontrivial A') := by
  classical
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientFirstVariation
    finiteFiberPushforwardCoefficient
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H),
      (if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B = b then
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
              (finiteEvenFourTorusDoubleRefinement H)
              energyIdentity energyNontrivial B A *
            finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H B
        else 0) -
      (if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B = b then
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
              (finiteEvenFourTorusDoubleRefinement H)
              energyIdentity energyNontrivial B A' *
            finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H B
        else 0)) =
      ∑ B : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H),
        if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B = b then
          (-(1 / 2 : ℝ) *
              (finiteEvenFourTorusZ2SpatialWilsonAction
                  (finiteEvenFourTorusDoubleRefinement H)
                  energyIdentity energyNontrivial A -
                finiteEvenFourTorusZ2SpatialWilsonAction
                  (finiteEvenFourTorusDoubleRefinement H)
                  energyIdentity energyNontrivial A')) *
            finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H
        else 0 := by
      apply Finset.sum_congr rfl
      intro B _hB
      by_cases hBfiber : finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B = b
      · rw [if_pos hBfiber, if_pos hBfiber,
          finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_eq_cardinality]
        rw [← sub_mul]
        rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation_sub_right]
      · rw [if_neg hBfiber, if_neg hBfiber, zero_sub, if_neg hBfiber]
    _ = (-(1 / 2 : ℝ) *
          (finiteEvenFourTorusZ2SpatialWilsonAction
              (finiteEvenFourTorusDoubleRefinement H)
              energyIdentity energyNontrivial A -
            finiteEvenFourTorusZ2SpatialWilsonAction
              (finiteEvenFourTorusDoubleRefinement H)
              energyIdentity energyNontrivial A') *
          finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H) *
        (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement H),
          if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B = b then
            (1 : ℝ) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _hB
      by_cases hBfiber : finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B = b
      · simp [hBfiber]
      · simp [hBfiber]
    _ = _ := by
      rw [finiteSurjectiveGroupHom_fiber_count
        (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H)
        (finiteEvenFourTorusZ2SliceConfigurationCoarseHom_surjective H) b]
      ring

/-- The beta-zero coarse first variation changes by the same constant embedding
scale times the coarse spatial-action defect. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightFirstVariation_sub
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A A' : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightFirstVariation
          H energyIdentity energyNontrivial A b -
      finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightFirstVariation
          H energyIdentity energyNontrivial A' b =
      -(1 / 2 : ℝ) *
        finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H *
        (finiteEvenFourTorusZ2SpatialWilsonAction
            H energyIdentity energyNontrivial
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A) -
          finiteEvenFourTorusZ2SpatialWilsonAction
            H energyIdentity energyNontrivial
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A')) := by
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightFirstVariation
  rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_eq_cardinality,
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_eq_cardinality]
  rw [← mul_sub]
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation_sub_right]
  ring

/-- At beta zero the fine analytic coefficient is exactly kernel multiplicity
times the constant embedding scale, independently of the evaluation point. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientAnalytic_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientAnalytic
        H energyIdentity energyNontrivial 0 A b =
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H *
        (Fintype.card
          (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker : ℝ) := by
  classical
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientAnalytic
    finiteFiberPushforwardCoefficient
  simp_rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_zero]
  simp_rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_eq_cardinality]
  calc
    (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H),
      if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B = b then
        1 * finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H
      else 0) =
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H *
        (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement H),
          if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B = b then
            (1 : ℝ) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _hB
      by_cases hBfiber : finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B = b
      · simp [hBfiber]
      · simp [hBfiber]
    _ = _ := by
      rw [finiteSurjectiveGroupHom_fiber_count
        (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H)
        (finiteEvenFourTorusZ2SliceConfigurationCoarseHom_surjective H) b]

/-- At beta zero the coarse analytic coefficient is the constant embedding
scale. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAnalytic_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAnalytic
        H energyIdentity energyNontrivial 0 A b =
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H := by
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAnalytic
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_zero]
  simp [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_eq_cardinality]

/-- Identity anchoring turns the whole beta-zero projective first variation into
one explicit fine-minus-coarse spatial Wilson action defect. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionFirstVariation_identityAnchor_eq_spatialDefect
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
        H energyIdentity energyNontrivial A 1 1 1 =
      (1 / 2 : ℝ) *
        (Fintype.card
          (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker : ℝ) *
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H) ^ 2 *
        ((finiteEvenFourTorusZ2SpatialWilsonAction
            H energyIdentity energyNontrivial
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A) -
          finiteEvenFourTorusZ2SpatialWilsonAction
            H energyIdentity energyNontrivial 1) -
        (finiteEvenFourTorusZ2SpatialWilsonAction
            (finiteEvenFourTorusDoubleRefinement H)
            energyIdentity energyNontrivial A -
          finiteEvenFourTorusZ2SpatialWilsonAction
            (finiteEvenFourTorusDoubleRefinement H)
            energyIdentity energyNontrivial 1)) := by
  let s := finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H
  let k : ℝ := Fintype.card
    (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker
  have hFine :=
    finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientFirstVariation_sub
      H energyIdentity energyNontrivial A 1 (1 : FiniteEvenFourTorusZ2SliceConfiguration H)
  have hCoarse :=
    finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightFirstVariation_sub
      H energyIdentity energyNontrivial A 1 (1 : FiniteEvenFourTorusZ2SliceConfiguration H)
  have hFineZeroA :=
    finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientAnalytic_zero
      H energyIdentity energyNontrivial A (1 : FiniteEvenFourTorusZ2SliceConfiguration H)
  have hFineZeroOne :=
    finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientAnalytic_zero
      H energyIdentity energyNontrivial
        (1 : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H))
        (1 : FiniteEvenFourTorusZ2SliceConfiguration H)
  have hCoarseZeroA :=
    finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAnalytic_zero
      H energyIdentity energyNontrivial A (1 : FiniteEvenFourTorusZ2SliceConfiguration H)
  have hCoarseZeroOne :=
    finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAnalytic_zero
      H energyIdentity energyNontrivial
        (1 : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H))
        (1 : FiniteEvenFourTorusZ2SliceConfiguration H)
  simp only [finiteEvenFourTorusZ2SliceConfigurationCoarseMap_one] at hCoarse
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
  rw [hFineZeroA, hFineZeroOne, hCoarseZeroA, hCoarseZeroOne]
  change
    _ = (1 / 2 : ℝ) * k * s ^ 2 * _
  change
    finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientFirstVariation
          H energyIdentity energyNontrivial A 1 * s +
        (s * k) *
          finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightFirstVariation
            H energyIdentity energyNontrivial 1 1 -
      (finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientFirstVariation
          H energyIdentity energyNontrivial 1 1 * s +
        (s * k) *
          finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightFirstVariation
            H energyIdentity energyNontrivial A 1) =
      (1 / 2 : ℝ) * k * s ^ 2 * _
  have hFine' :
      finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientFirstVariation
            H energyIdentity energyNontrivial A 1 -
        finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientFirstVariation
            H energyIdentity energyNontrivial 1 1 =
        -(1 / 2 : ℝ) * s * k *
          (finiteEvenFourTorusZ2SpatialWilsonAction
              (finiteEvenFourTorusDoubleRefinement H)
              energyIdentity energyNontrivial A -
            finiteEvenFourTorusZ2SpatialWilsonAction
              (finiteEvenFourTorusDoubleRefinement H)
              energyIdentity energyNontrivial 1) := by
    simpa [s, k] using hFine
  have hCoarse' :
      finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightFirstVariation
            H energyIdentity energyNontrivial A 1 -
        finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightFirstVariation
            H energyIdentity energyNontrivial 1 1 =
        -(1 / 2 : ℝ) * s *
          (finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial
              (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A) -
            finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial 1) := by
    simpa [s] using hCoarse
  linear_combination s * hFine' - (s * k) * hCoarse'

/-- If the fine configuration lies in the actual coarse-map kernel, only its
fine spatial Wilson action defect remains. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionFirstVariation_identityAnchor_eq_spatialDefect_of_coarseMap_eq_one
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (hA : finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A = 1) :
    finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
        H energyIdentity energyNontrivial A 1 1 1 =
      -(1 / 2 : ℝ) *
        (Fintype.card
          (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker : ℝ) *
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H) ^ 2 *
        (finiteEvenFourTorusZ2SpatialWilsonAction
            (finiteEvenFourTorusDoubleRefinement H)
            energyIdentity energyNontrivial A -
          finiteEvenFourTorusZ2SpatialWilsonAction
            (finiteEvenFourTorusDoubleRefinement H)
            energyIdentity energyNontrivial 1) := by
  rw [finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionFirstVariation_identityAnchor_eq_spatialDefect]
  rw [hA]
  ring

end

end MathlibAnalytic
end MGAP4D