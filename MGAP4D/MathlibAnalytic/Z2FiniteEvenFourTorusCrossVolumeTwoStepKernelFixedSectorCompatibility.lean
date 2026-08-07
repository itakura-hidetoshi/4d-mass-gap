import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeKernelFixedSectorCompatibility
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Exact pointwise normalization factor for the direct two-step invariant
embedding, expressed as the product of the two already-exact one-step factors
along the actual geometric coarse-map cocycle. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale
    (H : ℕ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) : ℝ :=
  finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale
      (finiteEvenFourTorusDoubleRefinement H) A *
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H
      (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
        (finiteEvenFourTorusDoubleRefinement H) A)

/-- The two-step pointwise scale is strictly positive. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale_pos
    (H : ℕ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) :
    0 < finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A := by
  exact mul_pos
    (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_pos
      (finiteEvenFourTorusDoubleRefinement H) A)
    (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_pos H
      (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
        (finiteEvenFourTorusDoubleRefinement H) A))

/-- Exact configuration formula for the direct two-step invariant embedding. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbedding_apply_coe_eq_scale_mul_rawPullback
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) :
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H f).1 A =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A *
        f.1
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
              (finiteEvenFourTorusDoubleRefinement H) A)) := by
  rw [← finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_twoStep_cocycle H f]
  rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_apply_coe_eq_scale_mul_rawPullback]
  rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_apply_coe_eq_scale_mul_rawPullback]
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale
  ring

/-- Raw direct two-step transfer residual between the coarsest and finest
actual invariant carriers. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) :=
  continuousLinearOperatorCrossCarrierResidualLinearMap
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H).toLinearMap

/-- Exact direct two-step normalized/raw decomposition, including the independent
normalization mismatch between the finest and coarsest raw transfer norms. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_raw_normalization_decomposition
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy •
        finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy +
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy -
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy) •
        ((finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H).toLinearMap.comp
          (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer
            H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap) := by
  apply LinearMap.ext
  intro f
  change
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
        β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H f) -
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          H β energyIdentity energyNontrivial hβ hEnergy f) = _
  rw [finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_eq_normalization_smul_raw]
  rw [finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_eq_normalization_smul_raw]
  change
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy : ℝ) •
        finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy
          (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H f) -
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H
        ((finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy : ℝ) •
          finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer
            H β energyIdentity energyNontrivial hβ hEnergy f) =
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
        β energyIdentity energyNontrivial hβ hEnergy : ℝ) •
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H))
            β energyIdentity energyNontrivial hβ hEnergy
            (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H f) -
          finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H
            (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer
              H β energyIdentity energyNontrivial hβ hEnergy f)) +
      ((finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy : ℝ) -
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy : ℝ)) •
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H
          (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer
            H β energyIdentity energyNontrivial hβ hEnergy f)
  rw [map_smul]
  module

/-- Exact actual finite-sum formula for the direct two-step raw transfer
residual.  The local elaboration budget only accommodates the large dependent
type expression produced by the two nested refinements; it changes no theorem
statement or mathematical assumption. -/
set_option maxHeartbeats 800000 in
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_apply_coe_eq_kernel_sums
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) :
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy f).1 A =
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
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A *
        (∑ b : FiniteEvenFourTorusZ2SliceConfiguration H,
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
              H β energyIdentity energyNontrivial hβ hEnergy b
              (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
                (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
                  (finiteEvenFourTorusDoubleRefinement H) A)) *
            f.1 b) := by
  change
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
        β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H f).1) A -
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer
          H β energyIdentity energyNontrivial hβ hEnergy f)).1 A = _
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
  rw [finiteKernelOperator_apply]
  simp_rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbedding_apply_coe_eq_scale_mul_rawPullback]
  rw [finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer_apply_coe]
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
  rw [finiteKernelOperator_apply]

/-- Direct two-step raw-kernel compatibility is exactly the displayed finite-sum
equation for every coarse invariant observable and finest configuration. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_kernelEquation
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      ∀ (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
        (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))),
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
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A *
          (∑ b : FiniteEvenFourTorusZ2SliceConfiguration H,
            finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
                H β energyIdentity energyNontrivial hβ hEnergy b
                (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
                  (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
                    (finiteEvenFourTorusDoubleRefinement H) A)) * f.1 b) := by
  constructor
  · intro h f A
    have hf := LinearMap.congr_fun h f
    have hA :
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy f).1 A = 0 := by
      simpa using congrArg
        (fun u : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)) => u.1 A) hf
    rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_apply_coe_eq_kernel_sums]
      at hA
    exact sub_eq_zero.mp hA
  · intro h
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    ext A
    rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_apply_coe_eq_kernel_sums]
    exact sub_eq_zero.mpr (h f A)

/-- Exact fixed-sector characterization for the direct two-step ground-projector
residual from Package F. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundProjectorIntertwiningResidual_eq_zero_iff_fixedSectorDecomposition
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundProjectorIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      FiniteDimensionalGroundProjectorDecompositionCompatible
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
          H β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H).toLinearMap := by
  exact finiteDimensionalGroundProjectorIntertwiningResidual_eq_zero_iff_decompositionCompatible
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H).toLinearMap

/-- Audit-visible direct two-step Package-G receipt. -/
structure Z2FiniteEvenFourTorusCrossVolumeTwoStepKernelFixedSectorCompatibilityPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  twoStepScale :
    FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)) → ℝ
  twoStepScale_eq : twoStepScale =
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H
  twoStepScale_pos : ∀ A, 0 < twoStepScale A
  rawTransferResidual :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
  rawTransferResidual_eq : rawTransferResidual =
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
      H β energyIdentity energyNontrivial hβ hEnergy
  normalizedTransferDecomposition :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy • rawTransferResidual +
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy -
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy) •
        ((finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H).toLinearMap.comp
          (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer
            H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap)
  rawKernelCriterion :
    rawTransferResidual = 0 ↔
      ∀ (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
        (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))),
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
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A *
          (∑ b : FiniteEvenFourTorusZ2SliceConfiguration H,
            finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
                H β energyIdentity energyNontrivial hβ hEnergy b
                (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
                  (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
                    (finiteEvenFourTorusDoubleRefinement H) A)) * f.1 b)
  groundFixedSectorCriterion :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundProjectorIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      FiniteDimensionalGroundProjectorDecompositionCompatible
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
          H β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H).toLinearMap
  liftedObstructionCriterion :
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy =
        finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundProjectorIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy

/-- Construct the complete direct two-step Package-G receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeTwoStepKernelFixedSectorCompatibilityPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeTwoStepKernelFixedSectorCompatibilityPackage
      H β energyIdentity energyNontrivial hβ hEnergy where
  twoStepScale := finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H
  twoStepScale_eq := rfl
  twoStepScale_pos := finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale_pos H
  rawTransferResidual :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
      H β energyIdentity energyNontrivial hβ hEnergy
  rawTransferResidual_eq := rfl
  normalizedTransferDecomposition :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_raw_normalization_decomposition
      H β energyIdentity energyNontrivial hβ hEnergy
  rawKernelCriterion :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_kernelEquation
      H β energyIdentity energyNontrivial hβ hEnergy
  groundFixedSectorCriterion :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundProjectorIntertwiningResidual_eq_zero_iff_fixedSectorDecomposition
      H β energyIdentity energyNontrivial hβ hEnergy
  liftedObstructionCriterion :=
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_eq_zero_iff_transfer_eq_ground
      H β energyIdentity energyNontrivial hβ hEnergy

/-- Final one-step/two-step Package G bundle. -/
structure Z2FiniteEvenFourTorusCrossVolumeKernelFixedSectorFullPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  oneStep :
    Z2FiniteEvenFourTorusCrossVolumeKernelFixedSectorCompatibilityPackage
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStep :
    Z2FiniteEvenFourTorusCrossVolumeTwoStepKernelFixedSectorCompatibilityPackage
      H β energyIdentity energyNontrivial hβ hEnergy

/-- Construct the full one-step/two-step Package G. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeKernelFixedSectorFullPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeKernelFixedSectorFullPackage
      H β energyIdentity energyNontrivial hβ hEnergy where
  oneStep := z2FiniteEvenFourTorusCrossVolumeKernelFixedSectorCompatibilityPackage
    H β energyIdentity energyNontrivial hβ hEnergy
  twoStep := z2FiniteEvenFourTorusCrossVolumeTwoStepKernelFixedSectorCompatibilityPackage
    H β energyIdentity energyNontrivial hβ hEnergy

end

end MathlibAnalytic
end MGAP4D
