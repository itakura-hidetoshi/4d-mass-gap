import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGaussProjectedOneSlabTransfer
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeOneSlabKernel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- Raw one-slab transfer after exact finite temporal-link summation. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2SliceHilbert H →L[ℝ]
      FiniteEvenFourTorusZ2SliceHilbert H :=
  finiteKernelOperator
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- Canonical op-norm normalization of the unfixed-gauge one-slab transfer. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2SliceHilbert H →L[ℝ]
      FiniteEvenFourTorusZ2SliceHilbert H :=
  finiteKernelNormalizedOperator
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- The physical temporal-link sum is exactly temporal-gauge transfer followed
by Gauss projection on the output boundary. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeRawTransfer_eq_Gauss_comp_temporal
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
        H β energyIdentity energyNontrivial hβ hEnergy =
      (finiteEvenFourTorusZ2GaussProjector H).comp
        (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
          H β energyIdentity energyNontrivial hβ hEnergy) := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
    finiteEvenFourTorusZ2GaussProjector
    finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
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
  exact finiteKernelOperator_rightAveraged_eq_projector_comp
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel

/-- Diagonal gauge invariance moves the same Gauss projection to the input
boundary. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeRawTransfer_eq_temporal_comp_Gauss
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
        H β energyIdentity energyNontrivial hβ hEnergy =
      (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
        H β energyIdentity energyNontrivial hβ hEnergy).comp
        (finiteEvenFourTorusZ2GaussProjector H) := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
    finiteEvenFourTorusZ2GaussProjector
    finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
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
  exact finiteKernelOperator_rightAveraged_eq_comp_projector
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_smul
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- On a Gauss-invariant input, the raw unfixed transfer agrees exactly with
the raw temporal-gauge transfer. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeRawTransfer_apply_invariant
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
        H β energyIdentity energyNontrivial hβ hEnergy f.1 =
      finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
        H β energyIdentity energyNontrivial hβ hEnergy f.1 := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeRawTransfer_eq_temporal_comp_Gauss]
  change
    finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteEvenFourTorusZ2GaussProjector H f.1) =
      finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
        H β energyIdentity energyNontrivial hβ hEnergy f.1
  unfold finiteEvenFourTorusZ2GaussProjector
  rw [finiteGroupAveragingProjector_eq_self_of_mem
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H) f.1 f.2]

/-- The raw unfixed transfer is nonzero because every diagonal averaged kernel
entry is strictly positive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer_ne_zero
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
      H β energyIdentity energyNontrivial hβ hEnergy ≠ 0 := by
  let A : FiniteEvenFourTorusZ2SliceConfiguration H := fun _ => 1
  apply finiteKernelOperator_ne_zero_of_diagonal_ne_zero
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
      H β energyIdentity energyNontrivial hβ hEnergy) A
  exact ne_of_gt
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_pos
      H β energyIdentity energyNontrivial hβ hEnergy A A)

/-- The raw unfixed-gauge transfer is symmetric. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer_isSymmetric
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
      H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.IsSymmetric :=
  finiteKernelOperator_isSymmetric
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_symmetric
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- The raw temporal-link averaged transfer is positive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer_quadratic_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceHilbert H) :
    0 ≤ inner ℝ
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
        H β energyIdentity energyNontrivial hβ hEnergy f) f := by
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
  exact finiteKernelOperator_rightAveraged_quadratic_nonneg
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_smul
      H β energyIdentity energyNontrivial hβ hEnergy) f

/-- The normalized unfixed-gauge transfer is symmetric. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer_isSymmetric
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
      H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.IsSymmetric :=
  finiteKernelNormalizedOperator_isSymmetric_of_kernel_symmetric
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_symmetric
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- The normalized unfixed-gauge transfer is positive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer_quadratic_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceHilbert H) :
    0 ≤ inner ℝ
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy f) f := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
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
  exact finiteKernelNormalizedOperator_rightAveraged_quadratic_nonneg
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_smul
      H β energyIdentity energyNontrivial hβ hEnergy) f

/-- The normalized unfixed transfer has operator norm exactly one. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer_norm_eq_one
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    ‖finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
      H β energyIdentity energyNontrivial hβ hEnergy‖ = 1 :=
  finiteKernelNormalizedOperator_norm_eq_one _
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer_ne_zero
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- The normalized unfixed transfer is contractive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer_norm_apply_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceHilbert H) :
    ‖finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
      H β energyIdentity energyNontrivial hβ hEnergy f‖ ≤ ‖f‖ :=
  finiteKernelNormalizedOperator_norm_apply_le _
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer_ne_zero
      H β energyIdentity energyNontrivial hβ hEnergy) f

/-- Every normalized unfixed-gauge transfer output is Gauss invariant. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer_mem_invariant
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceHilbert H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy f ∈
      finiteGroupInvariantSubmodule
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H) := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
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
  exact finiteKernelNormalizedOperator_rightAveraged_mem_invariant
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel f

/-- Compression of the normalized unfixed transfer to the invariant boundary
Hilbert space. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →L[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f =>
        ⟨finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
            H β energyIdentity energyNontrivial hβ hEnergy f.1,
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer_mem_invariant
            H β energyIdentity energyNontrivial hβ hEnergy f.1⟩
      map_add' := by
        intro f g
        apply Subtype.ext
        simp
      map_smul' := by
        intro c f
        apply Subtype.ext
        simp }

@[simp] theorem finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_apply_coe
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
      H β energyIdentity energyNontrivial hβ hEnergy f).1 =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy f.1 :=
  rfl

/-- Symmetry descends to the invariant unfixed transfer. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_isSymmetric
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
      H β energyIdentity energyNontrivial hβ hEnergy).toLinearMap.IsSymmetric := by
  intro f g
  exact finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer_isSymmetric
    H β energyIdentity energyNontrivial hβ hEnergy f.1 g.1

/-- Positivity descends to the invariant unfixed transfer. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_quadratic_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    0 ≤ inner ℝ
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy f) f :=
  finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer_quadratic_nonneg
    H β energyIdentity energyNontrivial hβ hEnergy f.1

/-- Contractivity descends to the invariant unfixed transfer. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_norm_apply_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    ‖finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
      H β energyIdentity energyNontrivial hβ hEnergy f‖ ≤ ‖f‖ :=
  finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer_norm_apply_le
    H β energyIdentity energyNontrivial hβ hEnergy f.1

/-- Natural powers of the ambient unfixed-gauge transfer. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeTransferSemigroup
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (n : ℕ) :
    FiniteEvenFourTorusZ2SliceHilbert H →L[ℝ]
      FiniteEvenFourTorusZ2SliceHilbert H :=
  finiteKernelNormalizedSemigroup
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
      H β energyIdentity energyNontrivial hβ hEnergy) n

/-- Additive natural time is composition for the unfixed transfer. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeTransferSemigroup_add
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (m n : ℕ) :
    finiteEvenFourTorusZ2UnfixedGaugeTransferSemigroup
        H β energyIdentity energyNontrivial hβ hEnergy (m + n) =
      (finiteEvenFourTorusZ2UnfixedGaugeTransferSemigroup
        H β energyIdentity energyNontrivial hβ hEnergy m).comp
      (finiteEvenFourTorusZ2UnfixedGaugeTransferSemigroup
        H β energyIdentity energyNontrivial hβ hEnergy n) :=
  finiteKernelNormalizedSemigroup_add _ m n

/-- Every ambient natural-time unfixed transfer remains contractive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeTransferSemigroup_norm_apply_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (n : ℕ)
    (f : FiniteEvenFourTorusZ2SliceHilbert H) :
    ‖finiteEvenFourTorusZ2UnfixedGaugeTransferSemigroup
      H β energyIdentity energyNontrivial hβ hEnergy n f‖ ≤ ‖f‖ :=
  finiteKernelNormalizedSemigroup_norm_apply_le _
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer_ne_zero
      H β energyIdentity energyNontrivial hβ hEnergy) n f

/-- Natural powers after compression to the invariant sector. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeInvariantTransferSemigroup
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (n : ℕ) :
    FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H →L[ℝ]
      FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
    H β energyIdentity energyNontrivial hβ hEnergy) ^ n

/-- Additive natural time remains composition after invariant compression. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariantTransferSemigroup_add
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (m n : ℕ) :
    finiteEvenFourTorusZ2UnfixedGaugeInvariantTransferSemigroup
        H β energyIdentity energyNontrivial hβ hEnergy (m + n) =
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantTransferSemigroup
        H β energyIdentity energyNontrivial hβ hEnergy m).comp
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantTransferSemigroup
        H β energyIdentity energyNontrivial hβ hEnergy n) := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeInvariantTransferSemigroup
  rw [pow_add]
  rfl

/-- Every compressed natural-time unfixed transfer remains contractive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariantTransferSemigroup_norm_apply_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (n : ℕ)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H) :
    ‖finiteEvenFourTorusZ2UnfixedGaugeInvariantTransferSemigroup
      H β energyIdentity energyNontrivial hβ hEnergy n f‖ ≤ ‖f‖ := by
  induction n with
  | zero =>
      simp [finiteEvenFourTorusZ2UnfixedGaugeInvariantTransferSemigroup]
  | succ n ih =>
      change
        ‖((finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          H β energyIdentity energyNontrivial hβ hEnergy) ^ (n + 1)) f‖ ≤ ‖f‖
      rw [pow_succ']
      exact
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_norm_apply_le
          H β energyIdentity energyNontrivial hβ hEnergy
          (((finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
            H β energyIdentity energyNontrivial hβ hEnergy) ^ n) f)).trans ih

end

end MathlibAnalytic
end MGAP4D
