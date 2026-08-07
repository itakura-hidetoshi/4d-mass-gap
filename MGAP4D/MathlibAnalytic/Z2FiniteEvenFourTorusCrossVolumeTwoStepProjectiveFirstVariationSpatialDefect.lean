import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeOneStepProjectiveFirstVariationSpatialDefect
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTwoStepProjectiveFirstVariation
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTwoStepBetaZeroFiberMultiplicityObstruction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

theorem finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseMap_fiberIndicatorSum
    (H : ℕ) (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H)),
      if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
            (finiteEvenFourTorusDoubleRefinement H) B) = b then (1 : ℝ) else 0) =
      (Fintype.card
        (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H).ker : ℝ) := by
  change
    (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H)),
      if (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H) B = b then
        (1 : ℝ) else 0) =
      (Fintype.card
        (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H).ker : ℝ)
  exact finiteSurjectiveGroupHom_fiber_count
    (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H)
    (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom_surjective H) b

theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientFirstVariation_sub
    (H : ℕ) (energyIdentity energyNontrivial : ℝ)
    (A A' : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientFirstVariation
          H energyIdentity energyNontrivial A b -
      finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientFirstVariation
          H energyIdentity energyNontrivial A' b =
      -(1 / 2 : ℝ) *
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale H *
        (Fintype.card
          (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H).ker : ℝ) *
        (finiteEvenFourTorusZ2SpatialWilsonAction
            (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H))
            energyIdentity energyNontrivial A -
          finiteEvenFourTorusZ2SpatialWilsonAction
            (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H))
            energyIdentity energyNontrivial A') := by
  classical
  let s := finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale H
  let d := -(1 / 2 : ℝ) *
    (finiteEvenFourTorusZ2SpatialWilsonAction
        (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H))
        energyIdentity energyNontrivial A -
      finiteEvenFourTorusZ2SpatialWilsonAction
        (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H))
        energyIdentity energyNontrivial A')
  have hpoint : ∀ B : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H)),
      (if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
            (finiteEvenFourTorusDoubleRefinement H) B) = b then
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
            (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H))
            energyIdentity energyNontrivial B A *
          finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H B
        else 0) -
      (if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
            (finiteEvenFourTorusDoubleRefinement H) B) = b then
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
            (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H))
            energyIdentity energyNontrivial B A' *
          finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H B
        else 0) =
      if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
            (finiteEvenFourTorusDoubleRefinement H) B) = b then d * s else 0 := by
    intro B
    by_cases hB : finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
          (finiteEvenFourTorusDoubleRefinement H) B) = b
    · rw [if_pos hB, if_pos hB, if_pos hB,
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale_eq_cardinality]
      rw [← sub_mul,
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation_sub_right]
    · simp [hB]
  have hcount := finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseMap_fiberIndicatorSum H b
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientFirstVariation
    finiteFiberPushforwardCoefficient
  rw [← Finset.sum_sub_distrib]
  simp_rw [hpoint]
  calc
    (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H)),
      if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
            (finiteEvenFourTorusDoubleRefinement H) B) = b then d * s else 0) =
      d * s *
        (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H)),
          if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
              (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
                (finiteEvenFourTorusDoubleRefinement H) B) = b then (1 : ℝ) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _
      by_cases hB : finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
            (finiteEvenFourTorusDoubleRefinement H) B) = b <;> simp [hB]
    _ = d * s *
        (Fintype.card
          (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H).ker : ℝ) := by
      rw [hcount]
    _ = _ := by
      dsimp [d, s]
      ring

theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightFirstVariation_sub
    (H : ℕ) (energyIdentity energyNontrivial : ℝ)
    (A A' : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightFirstVariation
          H energyIdentity energyNontrivial A b -
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightFirstVariation
          H energyIdentity energyNontrivial A' b =
      -(1 / 2 : ℝ) *
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale H *
        (finiteEvenFourTorusZ2SpatialWilsonAction H energyIdentity energyNontrivial
            (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H A) -
          finiteEvenFourTorusZ2SpatialWilsonAction H energyIdentity energyNontrivial
            (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H A')) := by
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightFirstVariation
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale_eq_cardinality,
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale_eq_cardinality]
  rw [← mul_sub]
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation_sub_right]
  simp only [finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom_apply]
  ring

theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic_zero
    (H : ℕ) (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic
        H energyIdentity energyNontrivial 0 A b =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale H *
        (Fintype.card
          (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H).ker : ℝ) := by
  classical
  have hcount := finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseMap_fiberIndicatorSum H b
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic
    finiteFiberPushforwardCoefficient
  simp_rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_zero]
  simp_rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale_eq_cardinality]
  calc
    (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H)),
      if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
            (finiteEvenFourTorusDoubleRefinement H) B) = b then
        1 * finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale H else 0) =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale H *
        (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H)),
          if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
              (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
                (finiteEvenFourTorusDoubleRefinement H) B) = b then (1 : ℝ) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _
      by_cases hB : finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
            (finiteEvenFourTorusDoubleRefinement H) B) = b <;> simp [hB]
    _ = _ := by rw [hcount]

theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic_zero
    (H : ℕ) (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic
        H energyIdentity energyNontrivial 0 A b =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale H := by
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale_eq_cardinality]
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_zero]
  ring

theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionFirstVariation_identityAnchor_eq_spatialDefect
    (H : ℕ) (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H))) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
        H energyIdentity energyNontrivial A 1 1 1 =
      (1 / 2 : ℝ) *
        (Fintype.card
          (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H).ker : ℝ) *
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale H) ^ 2 *
        ((finiteEvenFourTorusZ2SpatialWilsonAction H energyIdentity energyNontrivial
            (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H A) -
          finiteEvenFourTorusZ2SpatialWilsonAction H energyIdentity energyNontrivial 1) -
        (finiteEvenFourTorusZ2SpatialWilsonAction
            (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H))
            energyIdentity energyNontrivial A -
          finiteEvenFourTorusZ2SpatialWilsonAction
            (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H))
            energyIdentity energyNontrivial 1)) := by
  let s := finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale H
  let k : ℝ := Fintype.card
    (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H).ker
  let fA := finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientFirstVariation
    H energyIdentity energyNontrivial A (1 : FiniteEvenFourTorusZ2SliceConfiguration H)
  let f1 := finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientFirstVariation
    H energyIdentity energyNontrivial
      (1 : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H)))
      (1 : FiniteEvenFourTorusZ2SliceConfiguration H)
  let cA := finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightFirstVariation
    H energyIdentity energyNontrivial A (1 : FiniteEvenFourTorusZ2SliceConfiguration H)
  let c1 := finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightFirstVariation
    H energyIdentity energyNontrivial
      (1 : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H)))
      (1 : FiniteEvenFourTorusZ2SliceConfiguration H)
  have hFine : fA - f1 =
      -(1 / 2 : ℝ) * s * k *
        (finiteEvenFourTorusZ2SpatialWilsonAction
            (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H))
            energyIdentity energyNontrivial A -
          finiteEvenFourTorusZ2SpatialWilsonAction
            (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H))
            energyIdentity energyNontrivial 1) := by
    dsimp [fA, f1, s, k]
    exact finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientFirstVariation_sub
      H energyIdentity energyNontrivial A 1 (1 : FiniteEvenFourTorusZ2SliceConfiguration H)
  have hCoarse : cA - c1 =
      -(1 / 2 : ℝ) * s *
        (finiteEvenFourTorusZ2SpatialWilsonAction H energyIdentity energyNontrivial
            (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H A) -
          finiteEvenFourTorusZ2SpatialWilsonAction H energyIdentity energyNontrivial 1) := by
    dsimp [cA, c1, s]
    simpa using finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightFirstVariation_sub
      H energyIdentity energyNontrivial A 1 (1 : FiniteEvenFourTorusZ2SliceConfiguration H)
  have hFineZeroA := finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic_zero
    H energyIdentity energyNontrivial A (1 : FiniteEvenFourTorusZ2SliceConfiguration H)
  have hFineZeroOne := finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic_zero
    H energyIdentity energyNontrivial
      (1 : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H)))
      (1 : FiniteEvenFourTorusZ2SliceConfiguration H)
  have hCoarseZeroA := finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic_zero
    H energyIdentity energyNontrivial A (1 : FiniteEvenFourTorusZ2SliceConfiguration H)
  have hCoarseZeroOne := finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic_zero
    H energyIdentity energyNontrivial
      (1 : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H)))
      (1 : FiniteEvenFourTorusZ2SliceConfiguration H)
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
  rw [hFineZeroA, hFineZeroOne, hCoarseZeroA, hCoarseZeroOne]
  change fA * s + (s * k) * c1 - (f1 * s + (s * k) * cA) = _
  calc
    fA * s + (s * k) * c1 - (f1 * s + (s * k) * cA) =
        s * (fA - f1) - (s * k) * (cA - c1) := by ring
    _ = _ := by rw [hFine, hCoarse]; ring

theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionFirstVariation_identityAnchor_eq_spatialDefect_of_twoStepCoarseMap_eq_one
    (H : ℕ) (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H)))
    (hA : finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H A = 1) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
        H energyIdentity energyNontrivial A 1 1 1 =
      -(1 / 2 : ℝ) *
        (Fintype.card
          (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H).ker : ℝ) *
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingCardinalityScale H) ^ 2 *
        (finiteEvenFourTorusZ2SpatialWilsonAction
            (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H))
            energyIdentity energyNontrivial A -
          finiteEvenFourTorusZ2SpatialWilsonAction
            (finiteEvenFourTorusDoubleRefinement (finiteEvenFourTorusDoubleRefinement H))
            energyIdentity energyNontrivial 1) := by
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionFirstVariation_identityAnchor_eq_spatialDefect]
  rw [hA]
  ring

end

end MathlibAnalytic
end MGAP4D