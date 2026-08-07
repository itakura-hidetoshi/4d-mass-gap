import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeNormalizedConfigurationFiberTemporalLinkBoltzmann
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTwoStepConfigurationFiberKernelEvaluation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Exact direct two-step normalized kernel equation at one fixed finest
configuration.  The finest and coarsest op-norm scalars remain distinct. -/
def FiniteEvenFourTorusZ2TwoStepNormalizedKernelEquationAt
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) : Prop :=
  ∀ f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
        β energyIdentity energyNontrivial hβ hEnergy *
      (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)),
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H))
            β energyIdentity energyNontrivial hβ hEnergy B A *
          (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H B *
            f.1
              (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
                (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
                  (finiteEvenFourTorusDoubleRefinement H) B)))) =
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        H β energyIdentity energyNontrivial hβ hEnergy *
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A *
        (∑ b : FiniteEvenFourTorusZ2SliceConfiguration H,
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
              H β energyIdentity energyNontrivial hβ hEnergy b
              (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
                (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
                  (finiteEvenFourTorusDoubleRefinement H) A)) * f.1 b))

/-- Global direct two-step normalized kernel compatibility. -/
def FiniteEvenFourTorusZ2TwoStepNormalizedKernelEquation
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Prop :=
  ∀ A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)),
    FiniteEvenFourTorusZ2TwoStepNormalizedKernelEquationAt
      H β energyIdentity energyNontrivial hβ hEnergy A

/-- Scalar-weighted direct two-step orbit-fibre condition at one finest
configuration. -/
def FiniteEvenFourTorusZ2TwoStepNormalizedOrbitFiberBalanceAt
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) : Prop :=
  ∀ q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
        β energyIdentity energyNontrivial hβ hEnergy *
      finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q =
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        H β energyIdentity energyNontrivial hβ hEnergy *
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q

/-- Global scalar-weighted direct two-step orbit-fibre condition. -/
def FiniteEvenFourTorusZ2TwoStepNormalizedOrbitFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Prop :=
  ∀ A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)),
    FiniteEvenFourTorusZ2TwoStepNormalizedOrbitFiberBalanceAt
      H β energyIdentity energyNontrivial hβ hEnergy A

/-- The displayed scalar-valued direct two-step normalized kernel residual. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepNormalizedKernelResidualValue
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) : ℝ :=
  finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy *
    (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)),
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy B A *
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H B *
          f.1
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
              (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
                (finiteEvenFourTorusDoubleRefinement H) B)))) -
  finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
      H β energyIdentity energyNontrivial hβ hEnergy *
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A *
      (∑ b : FiniteEvenFourTorusZ2SliceConfiguration H,
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
            H β energyIdentity energyNontrivial hβ hEnergy b
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
              (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
                (finiteEvenFourTorusDoubleRefinement H) A)) * f.1 b))

set_option maxHeartbeats 800000 in
/-- Pointwise formula for the actual normalized direct two-step residual. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_apply_coe_eq_normalizedKernelResidualValue
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) :
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy f).1 A =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepNormalizedKernelResidualValue
        H β energyIdentity energyNontrivial hβ hEnergy f A := by
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_raw_normalization_decomposition]
  change
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
        β energyIdentity energyNontrivial hβ hEnergy *
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy f).1 A +
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy -
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy) *
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H
          (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer
            H β energyIdentity energyNontrivial hβ hEnergy f)).1 A = _
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepNormalizedKernelResidualValue
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_apply_coe_eq_kernel_sums]
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbedding_apply_coe_eq_scale_mul_rawPullback]
  rw [finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer_apply_coe]
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
  rw [finiteKernelOperator_apply]
  ring

/-- The direct two-step normalized residual vanishes exactly when the named
normalized kernel equation holds. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedKernelEquation
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      FiniteEvenFourTorusZ2TwoStepNormalizedKernelEquation
        H β energyIdentity energyNontrivial hβ hEnergy := by
  unfold FiniteEvenFourTorusZ2TwoStepNormalizedKernelEquation
  unfold FiniteEvenFourTorusZ2TwoStepNormalizedKernelEquationAt
  constructor
  · intro h A f
    have hf := LinearMap.congr_fun h f
    have hA :
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy f).1 A = 0 := by
      simpa using congrArg
        (fun u : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)) => u.1 A) hf
    rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_apply_coe_eq_normalizedKernelResidualValue]
      at hA
    unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepNormalizedKernelResidualValue at hA
    exact sub_eq_zero.mp hA
  · intro h
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    ext A
    rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_apply_coe_eq_normalizedKernelResidualValue]
    unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepNormalizedKernelResidualValue
    exact sub_eq_zero.mpr (h A f)

/-- At one finest evaluation configuration, the normalized direct two-step
kernel equation is exactly the scalar-weighted coarse orbit-fibre equation. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepNormalizedKernelEquation_iff_orbitFiberBalanceAt
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) :
    FiniteEvenFourTorusZ2TwoStepNormalizedKernelEquationAt
        H β energyIdentity energyNontrivial hβ hEnergy A ↔
      FiniteEvenFourTorusZ2TwoStepNormalizedOrbitFiberBalanceAt
        H β energyIdentity energyNontrivial hβ hEnergy A := by
  unfold FiniteEvenFourTorusZ2TwoStepNormalizedKernelEquationAt
  unfold FiniteEvenFourTorusZ2TwoStepNormalizedOrbitFiberBalanceAt
  have hGeneric :=
    finiteGroupInvariant_scaledCrossSum_eq_iff_scaledOrbitFiberSums
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H)
      (fun B : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)) =>
        finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
            (finiteEvenFourTorusDoubleRefinement H) B))
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
        β energyIdentity energyNontrivial hβ hEnergy)
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        H β energyIdentity energyNontrivial hβ hEnergy)
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A)
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A)
  constructor
  · intro h
    have hOrbit := hGeneric.mp (by
      intro f
      simpa only [finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight,
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight,
        Finset.mul_sum, mul_assoc] using h f)
    intro q
    simpa only [finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient,
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient] using hOrbit q
  · intro h
    have hFunctional := hGeneric.mpr (by
      intro q
      simpa only [finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient,
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient] using h q)
    intro f
    simpa only [finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight,
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight,
      Finset.mul_sum, mul_assoc] using hFunctional f

/-- Exact arbitrary-nonnegative-coupling criterion for the actual normalized
direct two-step cross-volume residual. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedOrbitFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      FiniteEvenFourTorusZ2TwoStepNormalizedOrbitFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy := by
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedKernelEquation]
  unfold FiniteEvenFourTorusZ2TwoStepNormalizedKernelEquation
  unfold FiniteEvenFourTorusZ2TwoStepNormalizedOrbitFiberBalance
  constructor
  · intro h A
    exact
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepNormalizedKernelEquation_iff_orbitFiberBalanceAt
        H β energyIdentity energyNontrivial hβ hEnergy A).1 (h A)
  · intro h A
    exact
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepNormalizedKernelEquation_iff_orbitFiberBalanceAt
        H β energyIdentity energyNontrivial hβ hEnergy A).2 (h A)

end

end MathlibAnalytic
end MGAP4D
