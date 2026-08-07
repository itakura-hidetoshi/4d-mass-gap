import MGAP4D.MathlibAnalytic.FiniteNormalizedOperatorCrossCarrierIntertwiningDecomposition
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeInvariantEmbeddingNormalization
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeGeometricOperatorCompatibility
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

namespace FiniteDimensionalSymmetricPositiveContractionData

variable
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (D : FiniteDimensionalSymmetricPositiveContractionData E)

/-- The canonical eigenvalue-one spectral projector is idempotent. -/
theorem groundSpectralProjector_idempotent
    (x : E) :
    D.groundSpectralProjector (D.groundSpectralProjector x) =
      D.groundSpectralProjector x := by
  rw [orthonormalDiagonalOperator_apply]
  rw [map_sum]
  calc
    ∑ i : Fin D.dimension,
        D.groundSpectralProjector
          (inner ℝ (D.eigenbasis i) x •
            (D.groundSpectralProjectorCoefficient i • D.eigenbasis i)) =
      ∑ i : Fin D.dimension,
        inner ℝ (D.eigenbasis i) x •
          (D.groundSpectralProjectorCoefficient i • D.eigenbasis i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [map_smul, map_smul, D.groundSpectralProjector_apply_eigenbasis]
        by_cases hi : D.eigenvalue i = 1
        · simp [groundSpectralProjectorCoefficient, hi]
        · simp [groundSpectralProjectorCoefficient, hi]
    _ = D.groundSpectralProjector x := by
      symm
      exact orthonormalDiagonalOperator_apply
        D.eigenbasis D.groundSpectralProjectorCoefficient x

/-- The complementary component is annihilated by the ground projector. -/
theorem groundSpectralProjector_sub_projector_eq_zero
    (x : E) :
    D.groundSpectralProjector (x - D.groundSpectralProjector x) = 0 := by
  rw [map_sub, D.groundSpectralProjector_idempotent]
  simp

end FiniteDimensionalSymmetricPositiveContractionData

/-- Compatibility of an arbitrary cross-carrier map with the eigenvalue-one
spectral decomposition: it must send the coarse ground-projector image into the
fine ground-projector image and the coarse complementary component into the
fine projector kernel. -/
def FiniteDimensionalGroundProjectorDecompositionCompatible
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [InnerProductSpace ℝ Ef]
    [FiniteDimensional ℝ Ef]
    [NormedAddCommGroup Ec]
    [InnerProductSpace ℝ Ec]
    [FiniteDimensional ℝ Ec]
    (Df : FiniteDimensionalSymmetricPositiveContractionData Ef)
    (Dc : FiniteDimensionalSymmetricPositiveContractionData Ec)
    (J : Ec →ₗ[ℝ] Ef) : Prop :=
  (∀ x : Ec,
    Df.groundSpectralProjector (J (Dc.groundSpectralProjector x)) =
      J (Dc.groundSpectralProjector x)) ∧
  (∀ x : Ec,
    Df.groundSpectralProjector
        (J (x - Dc.groundSpectralProjector x)) = 0)

/-- Exact necessary-and-sufficient fixed-sector characterization of ground
projector intertwining. -/
theorem finiteDimensionalGroundProjectorIntertwiningResidual_eq_zero_iff_decompositionCompatible
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [InnerProductSpace ℝ Ef]
    [FiniteDimensional ℝ Ef]
    [NormedAddCommGroup Ec]
    [InnerProductSpace ℝ Ec]
    [FiniteDimensional ℝ Ec]
    (Df : FiniteDimensionalSymmetricPositiveContractionData Ef)
    (Dc : FiniteDimensionalSymmetricPositiveContractionData Ec)
    (J : Ec →ₗ[ℝ] Ef) :
    finiteDimensionalGroundProjectorIntertwiningResidualLinearMap Df Dc J = 0 ↔
      FiniteDimensionalGroundProjectorDecompositionCompatible Df Dc J := by
  constructor
  · intro h
    have hintertwine :
        Df.groundSpectralProjector.toLinearMap.comp J =
          J.comp Dc.groundSpectralProjector.toLinearMap := by
      exact sub_eq_zero.mp h
    constructor
    · intro x
      have hx := LinearMap.congr_fun hintertwine (Dc.groundSpectralProjector x)
      change
        Df.groundSpectralProjector (J (Dc.groundSpectralProjector x)) =
          J (Dc.groundSpectralProjector (Dc.groundSpectralProjector x)) at hx
      rw [Dc.groundSpectralProjector_idempotent] at hx
      exact hx
    · intro x
      have hx := LinearMap.congr_fun hintertwine
        (x - Dc.groundSpectralProjector x)
      change
        Df.groundSpectralProjector
            (J (x - Dc.groundSpectralProjector x)) =
          J (Dc.groundSpectralProjector
            (x - Dc.groundSpectralProjector x)) at hx
      rw [Dc.groundSpectralProjector_sub_projector_eq_zero] at hx
      simpa using hx
  · rintro ⟨hImage, hComplement⟩
    apply sub_eq_zero.mpr
    apply LinearMap.ext
    intro x
    change
      Df.groundSpectralProjector (J x) = J (Dc.groundSpectralProjector x)
    have hxdecomp :
        J x =
          J (Dc.groundSpectralProjector x) +
            J (x - Dc.groundSpectralProjector x) := by
      module
    rw [hxdecomp, map_add, hImage x, hComplement x, add_zero]

/-- Actual raw unfixed-gauge transfer restricted to the Gauss-invariant
boundary Hilbert carrier. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →L[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f =>
        ⟨finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
            H β energyIdentity energyNontrivial hβ hEnergy f.1, by
          unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
          have hk :
              finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
                  H β energyIdentity energyNontrivial hβ hEnergy =
                finiteGroupRightAveragedKernel
                  (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
                  (FiniteEvenFourTorusZ2SliceConfiguration H)
                  (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
                    H β energyIdentity energyNontrivial hβ hEnergy).kernel := by
            funext A B
            exact finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_eq_rightAverage
              H β energyIdentity energyNontrivial hβ hEnergy A B
          rw [hk]
          exact finiteKernelOperator_rightAveraged_mem_invariant
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H)
            (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
              H β energyIdentity energyNontrivial hβ hEnergy).kernel f.1⟩
      map_add' := by
        intro f g
        apply Subtype.ext
        simp [finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer]
      map_smul' := by
        intro c f
        apply Subtype.ext
        simp [finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer] }

@[simp] theorem finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer_apply_coe
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer
      H β energyIdentity energyNontrivial hβ hEnergy f).1 =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
        H β energyIdentity energyNontrivial hβ hEnergy f.1 :=
  rfl

/-- Exact normalization scalar used by the actual unfixed-gauge transfer. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : ℝ :=
  ‖finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
    H β energyIdentity energyNontrivial hβ hEnergy‖⁻¹

/-- The actual invariant normalized transfer is exactly the ambient raw
transfer restricted to the invariant carrier, multiplied by the canonical
ambient op-norm normalization scalar. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_eq_normalization_smul_raw
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy •
        finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer
          H β energyIdentity energyNontrivial hβ hEnergy := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  change
    finiteKernelNormalizedOperator
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
          H β energyIdentity energyNontrivial hβ hEnergy) f.1 =
      ‖finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
        H β energyIdentity energyNontrivial hβ hEnergy‖⁻¹ •
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
          H β energyIdentity energyNontrivial hβ hEnergy f.1
  rfl

/-- Raw one-step transfer residual on the actual invariant carriers. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement H) :=
  continuousLinearOperatorCrossCarrierResidualLinearMap
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H).toLinearMap

/-- Exact decomposition of the actual normalized transfer residual into raw
kernel mismatch plus normalization mismatch. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_raw_normalization_decomposition
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy •
        finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy +
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy -
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy) •
        ((finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H).toLinearMap.comp
          (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer
            H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap) := by
  apply LinearMap.ext
  intro f
  rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap_apply]
  rw [finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_eq_normalization_smul_raw]
  rw [finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_eq_normalization_smul_raw]
  change
    _ • finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer
        (finiteEvenFourTorusDoubleRefinement H)
        β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f) -
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H
        (_ • finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer
          H β energyIdentity energyNontrivial hβ hEnergy f) = _
  rw [map_smul]
  module

/-- Exact configuration-level finite-sum formula for the raw transfer residual.
It contains the true pointwise embedding normalization factor and therefore is
the safe kernel-level cross-volume compatibility equation. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_apply_coe_eq_kernel_sums
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    (finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy f).1 A =
      (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H),
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
            (finiteEvenFourTorusDoubleRefinement H)
            β energyIdentity energyNontrivial hβ hEnergy B A *
          (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H B *
            f.1 (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B))) -
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A *
        (∑ b : FiniteEvenFourTorusZ2SliceConfiguration H,
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
              H β energyIdentity energyNontrivial hβ hEnergy b
              (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A) *
            f.1 b) := by
  change
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer
        (finiteEvenFourTorusDoubleRefinement H)
        β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f)).1 A -
      (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer
          H β energyIdentity energyNontrivial hβ hEnergy f)).1 A = _
  rw [finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer_apply_coe]
  rw [finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer_apply_coe]
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
  rw [finiteKernelOperator_apply, finiteKernelOperator_apply]
  rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_apply_coe_eq_scale_mul_rawPullback]
  apply congrArg₂ (· - ·)
  · apply Finset.sum_congr rfl
    intro B _hB
    rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_apply_coe_eq_scale_mul_rawPullback]
  · ring

/-- The raw transfer residual vanishes exactly when the displayed actual kernel
finite-sum equation holds for every invariant observable and every fine
configuration. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_kernelEquation
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      ∀ (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
        (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H)),
        (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement H),
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
              (finiteEvenFourTorusDoubleRefinement H)
              β energyIdentity energyNontrivial hβ hEnergy B A *
            (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H B *
              f.1 (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B))) =
        finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A *
          (∑ b : FiniteEvenFourTorusZ2SliceConfiguration H,
            finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
                H β energyIdentity energyNontrivial hβ hEnergy b
                (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A) * f.1 b) := by
  constructor
  · intro h f A
    have hf := LinearMap.congr_fun h f
    have hA := congrArg (fun u : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
      (finiteEvenFourTorusDoubleRefinement H) => u.1 A) hf
    rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_apply_coe_eq_kernel_sums]
      at hA
    simpa using sub_eq_zero.mp hA
  · intro h
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    ext A
    rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_apply_coe_eq_kernel_sums]
    exact sub_eq_zero.mpr (h f A)

/-- Exact actual fixed-sector criterion for the one-step ground-projector
residual from Package F. -/
theorem finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidual_eq_zero_iff_fixedSectorDecomposition
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      FiniteDimensionalGroundProjectorDecompositionCompatible
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
          H β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H).toLinearMap := by
  exact finiteDimensionalGroundProjectorIntertwiningResidual_eq_zero_iff_decompositionCompatible
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H).toLinearMap

/-- Audit-visible Package G joining the raw-kernel, normalization, and
fixed-sector characterizations of the actual one-step cross-volume residual. -/
structure Z2FiniteEvenFourTorusCrossVolumeKernelFixedSectorCompatibilityPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  rawTransferResidual :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →ₗ[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert
        (finiteEvenFourTorusDoubleRefinement H)
  rawTransferResidual_eq : rawTransferResidual =
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
      H β energyIdentity energyNontrivial hβ hEnergy
  normalizedTransferDecomposition :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy • rawTransferResidual +
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy -
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy) •
        ((finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H).toLinearMap.comp
          (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabRawTransfer
            H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap)
  rawKernelCriterion :
    rawTransferResidual = 0 ↔
      ∀ (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
        (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H)),
        (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement H),
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
              (finiteEvenFourTorusDoubleRefinement H)
              β energyIdentity energyNontrivial hβ hEnergy B A *
            (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H B *
              f.1 (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B))) =
        finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A *
          (∑ b : FiniteEvenFourTorusZ2SliceConfiguration H,
            finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
                H β energyIdentity energyNontrivial hβ hEnergy b
                (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A) * f.1 b)
  groundFixedSectorCriterion :
    finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      FiniteDimensionalGroundProjectorDecompositionCompatible
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
          H β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H).toLinearMap
  liftedObstructionCriterion :
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy =
        finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy

/-- Construct the complete actual Package-G receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeKernelFixedSectorCompatibilityPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeKernelFixedSectorCompatibilityPackage
      H β energyIdentity energyNontrivial hβ hEnergy where
  rawTransferResidual :=
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
      H β energyIdentity energyNontrivial hβ hEnergy
  rawTransferResidual_eq := rfl
  normalizedTransferDecomposition :=
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_raw_normalization_decomposition
      H β energyIdentity energyNontrivial hβ hEnergy
  rawKernelCriterion :=
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_kernelEquation
      H β energyIdentity energyNontrivial hβ hEnergy
  groundFixedSectorCriterion :=
    finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidual_eq_zero_iff_fixedSectorDecomposition
      H β energyIdentity energyNontrivial hβ hEnergy
  liftedObstructionCriterion :=
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_iff_transfer_eq_ground
      H β energyIdentity energyNontrivial hβ hEnergy

end

end MathlibAnalytic
end MGAP4D
