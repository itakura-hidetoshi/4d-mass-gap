import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeOneStepProjectiveFirstVariation
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTwoStepConfigurationFiberKernelEvaluation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Proof-free analytic direct finest-to-coarsest configuration-fibre
coefficient for the two-step comparison. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteFiberPushforwardCoefficient
    (fun B : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) =>
      finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
          (finiteEvenFourTorusDoubleRefinement H) B))
    (fun B : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) =>
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          energyIdentity energyNontrivial β B A *
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H B)
    b

/-- Proof-free analytic coarsest comparison coefficient for the direct
two-step problem. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A *
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic
      H energyIdentity energyNontrivial β b
      (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
          (finiteEvenFourTorusDoubleRefinement H) A))

/-- On the physical nonnegative-beta lane, the analytic direct fine
coefficient agrees exactly with the existing successive/direct coefficient. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic_eq_actual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic
        H energyIdentity energyNontrivial β A b =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A b := by
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient_eq_direct]
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic
  apply congrArg
    (fun w : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) → ℝ =>
      finiteFiberPushforwardCoefficient
        (fun B : FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H)) =>
          finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
              (finiteEvenFourTorusDoubleRefinement H) B)) w b)
  funext B
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_eq_kernel
    (finiteEvenFourTorusDoubleRefinement
      (finiteEvenFourTorusDoubleRefinement H))
    β energyIdentity energyNontrivial hβ hEnergy B A]

/-- On the physical nonnegative-beta lane, the analytic coarsest coefficient
agrees exactly with the existing direct two-step coefficient. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic_eq_actual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic
        H energyIdentity energyNontrivial β A b =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A b := by
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_eq_kernel
    H β energyIdentity energyNontrivial hβ hEnergy b
    (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
      (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
        (finiteEvenFourTorusDoubleRefinement H) A))]

/-- Exact beta-zero first variation of the direct finest-to-coarsest
configuration-fibre coefficient. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientFirstVariation
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteFiberPushforwardCoefficient
    (fun B : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) =>
      finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
          (finiteEvenFourTorusDoubleRefinement H) B))
    (fun B : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) =>
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          energyIdentity energyNontrivial B A *
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H B)
    b

/-- Exact beta-zero first variation of the coarsest direct two-step comparison
coefficient. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightFirstVariation
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A *
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticFirstVariation
      H energyIdentity energyNontrivial b
      (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
          (finiteEvenFourTorusDoubleRefinement H) A))

/-- Differentiate the direct finest-to-coarsest fibre coefficient in one
finite sum. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic_hasDerivAt_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    HasDerivAt
      (fun β : ℝ =>
        finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic
          H energyIdentity energyNontrivial β A b)
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientFirstVariation
        H energyIdentity energyNontrivial A b)
      0 := by
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientFirstVariation
  unfold finiteFiberPushforwardCoefficient
  exact HasDerivAt.fun_sum
    (u := Finset.univ)
    (fun B _hB => by
      by_cases hFiber :
          finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
              (finiteEvenFourTorusDoubleRefinement H) B) = b
      · simpa only [hFiber, if_pos] using
          (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_hasDerivAt_zero_named
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H))
            energyIdentity energyNontrivial B A).mul_const
              (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H B)
      · simpa only [hFiber, if_neg] using
          (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ))))

/-- Differentiate the coarsest direct two-step coefficient. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic_hasDerivAt_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    HasDerivAt
      (fun β : ℝ =>
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic
          H energyIdentity energyNontrivial β A b)
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightFirstVariation
        H energyIdentity energyNontrivial A b)
      0 := by
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightFirstVariation
  exact
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_hasDerivAt_zero_named
      H energyIdentity energyNontrivial b
      (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
          (finiteEvenFourTorusDoubleRefinement H) A))).const_mul
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A)

/-- Proof-free analytic extension of the global direct two-step projective
configuration-fibre obstruction. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionAnalytic
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : ℝ)
    (A A₀ : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b b₀ : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  projectiveCrossDifference
    (fun t : ℝ =>
      finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic
        H energyIdentity energyNontrivial t A b)
    (fun t : ℝ =>
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic
        H energyIdentity energyNontrivial t A₀ b₀)
    (fun t : ℝ =>
      finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic
        H energyIdentity energyNontrivial t A₀ b₀)
    (fun t : ℝ =>
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic
        H energyIdentity energyNontrivial t A b)
    β

/-- On `β ≥ 0`, the analytic direct two-step projective obstruction is exactly
Package O's normalization-independent actual obstruction. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionAnalytic_eq_actual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A A₀ : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b b₀ : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionAnalytic
        H energyIdentity energyNontrivial β A A₀ b b₀ =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstruction
        H β energyIdentity energyNontrivial hβ hEnergy A A₀ b b₀ := by
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionAnalytic
  unfold projectiveCrossDifference
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstruction
  unfold finiteScalarWeightedProjectiveFiberObstruction
  change
    finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic
          H energyIdentity energyNontrivial β A b *
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic
          H energyIdentity energyNontrivial β A₀ b₀ -
      finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic
          H energyIdentity energyNontrivial β A₀ b₀ *
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic
          H energyIdentity energyNontrivial β A b =
    finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A b *
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy A₀ b₀ -
      finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A₀ b₀ *
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy A b
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic_eq_actual
    H β energyIdentity energyNontrivial hβ hEnergy A b]
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic_eq_actual
    H β energyIdentity energyNontrivial hβ hEnergy A₀ b₀]
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic_eq_actual
    H β energyIdentity energyNontrivial hβ hEnergy A₀ b₀]
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic_eq_actual
    H β energyIdentity energyNontrivial hβ hEnergy A b]

/-- Named exact beta-zero first variation of the global direct two-step
projective obstruction. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A A₀ : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b b₀ : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientFirstVariation
        H energyIdentity energyNontrivial A b *
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic
        H energyIdentity energyNontrivial 0 A₀ b₀ +
    finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic
        H energyIdentity energyNontrivial 0 A b *
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightFirstVariation
        H energyIdentity energyNontrivial A₀ b₀ -
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientFirstVariation
        H energyIdentity energyNontrivial A₀ b₀ *
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic
        H energyIdentity energyNontrivial 0 A b +
    finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic
        H energyIdentity energyNontrivial 0 A₀ b₀ *
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightFirstVariation
        H energyIdentity energyNontrivial A b)

/-- Exact beta-zero first variation of the actual direct two-step global
projective obstruction. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionAnalytic_hasDerivAt_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A A₀ : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b b₀ : FiniteEvenFourTorusZ2SliceConfiguration H) :
    HasDerivAt
      (fun β : ℝ =>
        finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionAnalytic
          H energyIdentity energyNontrivial β A A₀ b b₀)
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
        H energyIdentity energyNontrivial A A₀ b b₀)
      0 := by
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionAnalytic
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
  exact projectiveCrossDifference_hasDerivAt_zero
    (fun t : ℝ =>
      finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic
        H energyIdentity energyNontrivial t A b)
    (fun t : ℝ =>
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic
        H energyIdentity energyNontrivial t A₀ b₀)
    (fun t : ℝ =>
      finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic
        H energyIdentity energyNontrivial t A₀ b₀)
    (fun t : ℝ =>
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic
        H energyIdentity energyNontrivial t A b)
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientFirstVariation
      H energyIdentity energyNontrivial A b)
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightFirstVariation
      H energyIdentity energyNontrivial A₀ b₀)
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientFirstVariation
      H energyIdentity energyNontrivial A₀ b₀)
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightFirstVariation
      H energyIdentity energyNontrivial A b)
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic_hasDerivAt_zero
      H energyIdentity energyNontrivial A b)
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic_hasDerivAt_zero
      H energyIdentity energyNontrivial A₀ b₀)
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficientAnalytic_hasDerivAt_zero
      H energyIdentity energyNontrivial A₀ b₀)
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAnalytic_hasDerivAt_zero
      H energyIdentity energyNontrivial A b)

/-- Package M implies that every identity-anchored analytic direct two-step
projective obstruction is exactly zero at beta zero. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionAnalytic_zero_identityAnchor
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionAnalytic
      H energyIdentity energyNontrivial 0 A 1 b 1 = 0 := by
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionAnalytic_eq_actual
    H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy A 1 b 1]
  have hCriterion :=
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_eq_zero_iff_globalIdentityAnchor_and_projective
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy).1
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_beta_zero_eq_zero
        H energyIdentity energyNontrivial hEnergy)
  exact hCriterion.2 A b

/-- Audit-visible direct two-step Package-P receipt. -/
structure Z2FiniteEvenFourTorusCrossVolumeTwoStepProjectiveFirstVariationPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  analyticAgreement :
    ∀ (β : ℝ) (hβ : 0 ≤ β)
      (A : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)))
      (b : FiniteEvenFourTorusZ2SliceConfiguration H),
      finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionAnalytic
          H energyIdentity energyNontrivial β A 1 b 1 =
        finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstruction
          H β energyIdentity energyNontrivial hβ hEnergy A 1 b 1
  betaZeroValue :
    ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)))
      (b : FiniteEvenFourTorusZ2SliceConfiguration H),
      finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionAnalytic
        H energyIdentity energyNontrivial 0 A 1 b 1 = 0
  betaZeroDerivative :
    ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)))
      (b : FiniteEvenFourTorusZ2SliceConfiguration H),
      HasDerivAt
        (fun β : ℝ =>
          finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionAnalytic
            H energyIdentity energyNontrivial β A 1 b 1)
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
          H energyIdentity energyNontrivial A 1 b 1)
        0

/-- Construct the direct two-step Package-P first-variation receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeTwoStepProjectiveFirstVariationPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeTwoStepProjectiveFirstVariationPackage
      H energyIdentity energyNontrivial hEnergy where
  analyticAgreement := fun β hβ A b =>
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionAnalytic_eq_actual
      H β energyIdentity energyNontrivial hβ hEnergy A 1 b 1
  betaZeroValue :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionAnalytic_zero_identityAnchor
      H energyIdentity energyNontrivial hEnergy
  betaZeroDerivative := fun A b =>
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionAnalytic_hasDerivAt_zero
      H energyIdentity energyNontrivial A 1 b 1

/-- Complete Package-P receipt, bundling both one-step and direct two-step
normalization-free beta-zero projective first variations. -/
structure Z2FiniteEvenFourTorusCrossVolumeProjectiveFirstVariationPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  oneStep : Z2FiniteEvenFourTorusCrossVolumeOneStepProjectiveFirstVariationPackage
    H energyIdentity energyNontrivial hEnergy
  twoStep : Z2FiniteEvenFourTorusCrossVolumeTwoStepProjectiveFirstVariationPackage
    H energyIdentity energyNontrivial hEnergy

/-- Construct the complete Package-P first-variation receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeProjectiveFirstVariationPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeProjectiveFirstVariationPackage
      H energyIdentity energyNontrivial hEnergy where
  oneStep := z2FiniteEvenFourTorusCrossVolumeOneStepProjectiveFirstVariationPackage
    H energyIdentity energyNontrivial hEnergy
  twoStep := z2FiniteEvenFourTorusCrossVolumeTwoStepProjectiveFirstVariationPackage
    H energyIdentity energyNontrivial hEnergy

end

end MathlibAnalytic
end MGAP4D