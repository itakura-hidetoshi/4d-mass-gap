import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeOneSlabKernelAnalytic
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeNormalizedGlobalProjectiveFiberObstruction
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeBetaZeroNormalizedTransferIntertwining
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Exact beta-zero first variation coefficient of the proof-free analytic
one-slab kernel. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
    ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
      -finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
        H 0 energyIdentity energyNontrivial U A B

/-- The analytic one-slab kernel has the named exact first variation. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_hasDerivAt_zero_named
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    HasDerivAt
      (fun β : ℝ =>
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic
          H energyIdentity energyNontrivial β A B)
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
        H energyIdentity energyNontrivial A B)
      0 := by
  exact finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_hasDerivAt_zero
    H energyIdentity energyNontrivial A B

/-- Proof-free analytic extension of the actual one-step fine configuration-
fibre coefficient. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientAnalytic
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteFiberPushforwardCoefficient
    (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
    (fun B : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H) =>
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic
          (finiteEvenFourTorusDoubleRefinement H)
          energyIdentity energyNontrivial β B A *
        finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H B)
    b

/-- Proof-free analytic extension of the actual one-step coarse comparison
coefficient. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAnalytic
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A *
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic
      H energyIdentity energyNontrivial β b
      (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A)

/-- On `β ≥ 0`, the proof-free fine coefficient agrees exactly with the
existing physical one-step configuration-fibre coefficient. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientAnalytic_eq_actual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientAnalytic
        H energyIdentity energyNontrivial β A b =
      finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A b := by
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientAnalytic
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
  apply congrArg
    (fun w : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H) → ℝ =>
      finiteFiberPushforwardCoefficient
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H) w b)
  funext B
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepFineKernelWeight
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_eq_kernel
    (finiteEvenFourTorusDoubleRefinement H)
    β energyIdentity energyNontrivial hβ hEnergy B A]

/-- On `β ≥ 0`, the proof-free coarse coefficient agrees exactly with the
existing physical one-step coarse coefficient. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAnalytic_eq_actual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAnalytic
        H energyIdentity energyNontrivial β A b =
      finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A b := by
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAnalytic
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_eq_kernel
    H β energyIdentity energyNontrivial hβ hEnergy b
    (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A)]

/-- Exact first variation of the analytic one-step fine configuration-fibre
coefficient. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientFirstVariation
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteFiberPushforwardCoefficient
    (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
    (fun B : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H) =>
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
          (finiteEvenFourTorusDoubleRefinement H)
          energyIdentity energyNontrivial B A *
        finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H B)
    b

/-- Exact first variation of the analytic one-step coarse comparison
coefficient. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightFirstVariation
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A *
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
      H energyIdentity energyNontrivial b
      (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A)

/-- Differentiate the entire fine coarse-map fibre by differentiating each
finite kernel coefficient. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientAnalytic_hasDerivAt_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    HasDerivAt
      (fun β : ℝ =>
        finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientAnalytic
          H energyIdentity energyNontrivial β A b)
      (finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientFirstVariation
        H energyIdentity energyNontrivial A b)
      0 := by
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientAnalytic
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientFirstVariation
  unfold finiteFiberPushforwardCoefficient
  exact HasDerivAt.fun_sum
    (u := Finset.univ)
    (fun B _hB => by
      by_cases hFiber : finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B = b
      · rw [if_pos hFiber, if_pos hFiber]
        exact
          (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_hasDerivAt_zero_named
            (finiteEvenFourTorusDoubleRefinement H)
            energyIdentity energyNontrivial B A).mul_const
              (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H B)
      · rw [if_neg hFiber, if_neg hFiber]
        exact hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ)))

/-- Differentiate the coarse one-step coefficient. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAnalytic_hasDerivAt_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    HasDerivAt
      (fun β : ℝ =>
        finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAnalytic
          H energyIdentity energyNontrivial β A b)
      (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightFirstVariation
        H energyIdentity energyNontrivial A b)
      0 := by
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAnalytic
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightFirstVariation
  exact
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_hasDerivAt_zero_named
      H energyIdentity energyNontrivial b
      (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A)).const_mul
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A)

/-- Proof-free analytic extension of the global one-step projective
configuration-fibre obstruction. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionAnalytic
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : ℝ)
    (A A₀ : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b b₀ : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  projectiveCrossDifference
    (fun t : ℝ =>
      finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientAnalytic
        H energyIdentity energyNontrivial t A b)
    (fun t : ℝ =>
      finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAnalytic
        H energyIdentity energyNontrivial t A₀ b₀)
    (fun t : ℝ =>
      finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientAnalytic
        H energyIdentity energyNontrivial t A₀ b₀)
    (fun t : ℝ =>
      finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAnalytic
        H energyIdentity energyNontrivial t A b)
    β

/-- On `β ≥ 0`, the analytic projective obstruction agrees with the actual
normalization-independent obstruction from Package O. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionAnalytic_eq_actual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A A₀ : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b b₀ : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionAnalytic
        H energyIdentity energyNontrivial β A A₀ b b₀ =
      finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstruction
        H β energyIdentity energyNontrivial hβ hEnergy A A₀ b b₀ := by
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionAnalytic
  unfold projectiveCrossDifference
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstruction
  unfold finiteScalarWeightedProjectiveFiberObstruction
  rw [finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientAnalytic_eq_actual
    H β energyIdentity energyNontrivial hβ hEnergy A b]
  rw [finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAnalytic_eq_actual
    H β energyIdentity energyNontrivial hβ hEnergy A₀ b₀]
  rw [finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientAnalytic_eq_actual
    H β energyIdentity energyNontrivial hβ hEnergy A₀ b₀]
  rw [finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAnalytic_eq_actual
    H β energyIdentity energyNontrivial hβ hEnergy A b]

/-- Named exact beta-zero first variation of the global one-step projective
obstruction. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A A₀ : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b b₀ : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientFirstVariation
        H energyIdentity energyNontrivial A b *
      finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAnalytic
        H energyIdentity energyNontrivial 0 A₀ b₀ +
    finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientAnalytic
        H energyIdentity energyNontrivial 0 A b *
      finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightFirstVariation
        H energyIdentity energyNontrivial A₀ b₀ -
    (finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientFirstVariation
        H energyIdentity energyNontrivial A₀ b₀ *
      finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAnalytic
        H energyIdentity energyNontrivial 0 A b +
    finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientAnalytic
        H energyIdentity energyNontrivial 0 A₀ b₀ *
      finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightFirstVariation
        H energyIdentity energyNontrivial A b)

/-- Exact first variation at beta zero of the actual one-step global
projective obstruction, expressed only through finite action moments and
zero-coupling coefficient values. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionAnalytic_hasDerivAt_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A A₀ : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b b₀ : FiniteEvenFourTorusZ2SliceConfiguration H) :
    HasDerivAt
      (fun β : ℝ =>
        finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionAnalytic
          H energyIdentity energyNontrivial β A A₀ b b₀)
      (finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
        H energyIdentity energyNontrivial A A₀ b b₀)
      0 := by
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionAnalytic
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
  exact projectiveCrossDifference_hasDerivAt_zero
    (fun t : ℝ =>
      finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientAnalytic
        H energyIdentity energyNontrivial t A b)
    (fun t : ℝ =>
      finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAnalytic
        H energyIdentity energyNontrivial t A₀ b₀)
    (fun t : ℝ =>
      finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientAnalytic
        H energyIdentity energyNontrivial t A₀ b₀)
    (fun t : ℝ =>
      finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAnalytic
        H energyIdentity energyNontrivial t A b)
    (finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientFirstVariation
      H energyIdentity energyNontrivial A b)
    (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightFirstVariation
      H energyIdentity energyNontrivial A₀ b₀)
    (finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientFirstVariation
      H energyIdentity energyNontrivial A₀ b₀)
    (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightFirstVariation
      H energyIdentity energyNontrivial A b)
    (finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientAnalytic_hasDerivAt_zero
      H energyIdentity energyNontrivial A b)
    (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAnalytic_hasDerivAt_zero
      H energyIdentity energyNontrivial A₀ b₀)
    (finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficientAnalytic_hasDerivAt_zero
      H energyIdentity energyNontrivial A₀ b₀)
    (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAnalytic_hasDerivAt_zero
      H energyIdentity energyNontrivial A b)

/-- Package M implies that every identity-anchored analytic one-step
projective obstruction is exactly zero at beta zero. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionAnalytic_zero_identityAnchor
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionAnalytic
      H energyIdentity energyNontrivial 0 A 1 b 1 = 0 := by
  rw [finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionAnalytic_eq_actual
    H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy A 1 b 1]
  have hCriterion :=
    (finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_eq_zero_iff_globalIdentityAnchor_and_projective
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy).1
      (finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_beta_zero_eq_zero
        H energyIdentity energyNontrivial hEnergy)
  exact hCriterion.2 A b

/-- Audit-visible one-step Package-P receipt. -/
structure Z2FiniteEvenFourTorusCrossVolumeOneStepProjectiveFirstVariationPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  analyticAgreement : ∀ (β : ℝ) (hβ : 0 ≤ β) A b,
    finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionAnalytic
        H energyIdentity energyNontrivial β A 1 b 1 =
      finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstruction
        H β energyIdentity energyNontrivial hβ hEnergy A 1 b 1
  betaZeroValue : ∀ A b,
    finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionAnalytic
      H energyIdentity energyNontrivial 0 A 1 b 1 = 0
  betaZeroDerivative : ∀ A b,
    HasDerivAt
      (fun β : ℝ =>
        finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionAnalytic
          H energyIdentity energyNontrivial β A 1 b 1)
      (finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
        H energyIdentity energyNontrivial A 1 b 1)
      0

/-- Construct the one-step Package-P first-variation receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeOneStepProjectiveFirstVariationPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeOneStepProjectiveFirstVariationPackage
      H energyIdentity energyNontrivial hEnergy where
  analyticAgreement := fun β hβ A b =>
    finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionAnalytic_eq_actual
      H β energyIdentity energyNontrivial hβ hEnergy A 1 b 1
  betaZeroValue :=
    finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionAnalytic_zero_identityAnchor
      H energyIdentity energyNontrivial hEnergy
  betaZeroDerivative := fun A b =>
    finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionAnalytic_hasDerivAt_zero
      H energyIdentity energyNontrivial A 1 b 1

end

end MathlibAnalytic
end MGAP4D