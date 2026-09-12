import MGAP4D.MathlibAnalytic.FiniteGroupScalarWeightedOrbitFiberCriterion
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeOneStepConfigurationFiberKernelEvaluation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Exact normalized kernel equation at one fixed fine evaluation
configuration.  The actual fine/coarse op-norm scalars remain distinct. -/
def FiniteEvenFourTorusZ2OneStepNormalizedKernelEquationAt
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) : Prop :=
  ∀ f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        (finiteEvenFourTorusDoubleRefinement H)
        β energyIdentity energyNontrivial hβ hEnergy *
      (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H),
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
            (finiteEvenFourTorusDoubleRefinement H)
            β energyIdentity energyNontrivial hβ hEnergy B A *
          (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H B *
            f.1 (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B))) =
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        H β energyIdentity energyNontrivial hβ hEnergy *
      (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A *
        (∑ b : FiniteEvenFourTorusZ2SliceConfiguration H,
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
              H β energyIdentity energyNontrivial hβ hEnergy b
              (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A) * f.1 b))

/-- Global one-step normalized kernel compatibility. -/
def FiniteEvenFourTorusZ2OneStepNormalizedKernelEquation
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Prop :=
  ∀ A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H),
    FiniteEvenFourTorusZ2OneStepNormalizedKernelEquationAt
      H β energyIdentity energyNontrivial hβ hEnergy A

/-- Exact scalar-weighted orbit-fibre condition for the normalized one-step
transfer. -/
def FiniteEvenFourTorusZ2OneStepNormalizedOrbitFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Prop :=
  ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H),
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        (finiteEvenFourTorusDoubleRefinement H)
        β energyIdentity energyNontrivial hβ hEnergy *
      finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q =
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        H β energyIdentity energyNontrivial hβ hEnergy *
      finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q

/-- Exact pointwise finite-sum formula for the actual independently
operator-norm-normalized one-step cross-volume residual. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_apply_coe_eq_normalized_kernel_sums
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    (finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy f).1 A =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy *
        (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement H),
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
              (finiteEvenFourTorusDoubleRefinement H)
              β energyIdentity energyNontrivial hβ hEnergy B A *
            (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H B *
              f.1 (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B))) -
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy *
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A *
          (∑ b : FiniteEvenFourTorusZ2SliceConfiguration H,
            finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
                H β energyIdentity energyNontrivial hβ hEnergy b
                (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A) * f.1 b)) := by
  rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_raw_normalization_decomposition]
  change
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        (finiteEvenFourTorusDoubleRefinement H)
        β energyIdentity energyNontrivial hβ hEnergy *
      (finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy f).1 A +
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy -
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy) *
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H
          (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer
            H β energyIdentity energyNontrivial hβ hEnergy f)).1 A = _
  rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_apply_coe_eq_kernel_sums]
  rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_apply_coe_eq_scale_mul_rawPullback]
  rw [finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer_apply_coe]
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
  rw [finiteKernelOperator_apply]
  ring

/-- Vanishing of the actual normalized one-step residual is exactly the named
finite normalized kernel equation. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedKernelEquation
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      FiniteEvenFourTorusZ2OneStepNormalizedKernelEquation
        H β energyIdentity energyNontrivial hβ hEnergy := by
  unfold FiniteEvenFourTorusZ2OneStepNormalizedKernelEquation
  unfold FiniteEvenFourTorusZ2OneStepNormalizedKernelEquationAt
  constructor
  · intro h A f
    have hf := LinearMap.congr_fun h f
    have hA :
        (finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy f).1 A = 0 := by
      simpa using congrArg
        (fun u : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
          (finiteEvenFourTorusDoubleRefinement H) => u.1 A) hf
    rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_apply_coe_eq_normalized_kernel_sums]
      at hA
    exact sub_eq_zero.mp hA
  · intro h
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    ext A
    rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_apply_coe_eq_normalized_kernel_sums]
    exact sub_eq_zero.mpr (h A f)

/-- At one fixed fine evaluation configuration, the named normalized kernel
equation is exactly the scalar-weighted orbit-fibre equation. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepNormalizedKernelEquation_iff_orbitFiberCoefficients
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    FiniteEvenFourTorusZ2OneStepNormalizedKernelEquationAt
        H β energyIdentity energyNontrivial hβ hEnergy A ↔
      ∀ q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H,
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            (finiteEvenFourTorusDoubleRefinement H)
            β energyIdentity energyNontrivial hβ hEnergy *
          finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q =
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            H β energyIdentity energyNontrivial hβ hEnergy *
          finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q := by
  unfold FiniteEvenFourTorusZ2OneStepNormalizedKernelEquationAt
  have hGeneric :=
    finiteGroupInvariant_scaledCrossSum_eq_iff_scaledOrbitFiberSums
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H)
      (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        (finiteEvenFourTorusDoubleRefinement H)
        β energyIdentity energyNontrivial hβ hEnergy)
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        H β energyIdentity energyNontrivial hβ hEnergy)
      (finiteEvenFourTorusZ2GaugeInvariantOneStepFineKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A)
      (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A)
  constructor
  · intro h
    have hOrbit := hGeneric.mp (by
      intro f
      simpa only [finiteEvenFourTorusZ2GaugeInvariantOneStepFineKernelWeight,
        finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight,
        Finset.mul_sum, mul_assoc] using h f)
    intro q
    simpa only [finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient,
      finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient] using hOrbit q
  · intro h
    have hFunctional := hGeneric.mpr (by
      intro q
      simpa only [finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient,
        finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient] using h q)
    intro f
    simpa only [finiteEvenFourTorusZ2GaugeInvariantOneStepFineKernelWeight,
      finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight,
      Finset.mul_sum, mul_assoc] using hFunctional f

/-- Exact one-step criterion for actual operator-norm-normalized cross-volume
intertwining at arbitrary nonnegative coupling. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedOrbitFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      FiniteEvenFourTorusZ2OneStepNormalizedOrbitFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy := by
  rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedKernelEquation]
  unfold FiniteEvenFourTorusZ2OneStepNormalizedKernelEquation
  unfold FiniteEvenFourTorusZ2OneStepNormalizedOrbitFiberBalance
  constructor
  · intro h A
    exact
      (finiteEvenFourTorusZ2GaugeInvariantOneStepNormalizedKernelEquation_iff_orbitFiberCoefficients
        H β energyIdentity energyNontrivial hβ hEnergy A).1
        (h A)
  · intro h A
    exact
      (finiteEvenFourTorusZ2GaugeInvariantOneStepNormalizedKernelEquation_iff_orbitFiberCoefficients
        H β energyIdentity energyNontrivial hβ hEnergy A).2
        (h A)

end

end MathlibAnalytic
end MGAP4D
