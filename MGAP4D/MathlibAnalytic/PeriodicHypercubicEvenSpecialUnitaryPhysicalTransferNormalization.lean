import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenvector
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance periodicHypercubicEvenSpecialUnitarySpatialSliceHaarNormalization_isProbability
    (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarNormalization_isProbability
    (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

/-- The literal complete one-slab Boltzmann kernel is integrable on product
normalized Haar probability. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pair_integrable
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  have hmeas :
      AEStronglyMeasurable
        (fun p :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta).measurable.aestronglyMeasurable
  apply Integrable.of_bound hmeas 1
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_pos
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H N beta p.1 p.2)]
  exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_le_one
    H N hN beta hbeta p.1 p.2

/-- The product-Haar average of the actual one-slab kernel is strictly positive. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pair_integral_pos
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 < ∫ p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta p.1 p.2
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  let pairMeasure := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let k := fun p :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta p.1 p.2
  have hk_nonneg : 0 ≤ k := fun p =>
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H N beta p.1 p.2).le
  have hk_int : Integrable k pairMeasure := by
    simpa [pairMeasure, k] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pair_integrable
        H N hN beta hbeta
  rw [integral_pos_iff_support_of_nonneg hk_nonneg hk_int]
  have hsupp : Function.support k = Set.univ := by
    ext p
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H N beta p.1 p.2).ne'
  rw [hsupp]
  simp [pairMeasure]

/-- Constant-one pairing equals the literal product-Haar kernel integral. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_const_one_eq_integral
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta)
        (Lp.const 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) (1 : ℝ))
        (Lp.const 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) (1 : ℝ)) =
      ∫ p :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta p.1 p.2
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let oneL2 : Lp ℝ 2 μ := Lp.const 2 μ (1 : ℝ)
  let K :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
      H N hN beta hbeta
  change inner ℝ K (realL2ExternalTensor oneL2 oneL2) =
    ∫ p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta p.1 p.2
      ∂(μ.prod μ)
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  have hK :
      K =ᵐ[μ.prod μ]
        fun p => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2 := by
    simpa [K, μ, periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure] using
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
        H N hN beta hbeta)
  have hTensor := realL2ExternalTensor_coeFn oneL2 oneL2
  have hOne : oneL2 =ᵐ[μ] fun _ => (1 : ℝ) := by
    simpa [oneL2] using (Lp.coeFn_const (μ := μ) (p := 2) (c := (1 : ℝ)))
  have hOneFst := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq hOne
  have hOneSnd := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq hOne
  filter_upwards [hK, hTensor, hOneFst, hOneSnd] with p hk ht h1 h2
  have ht' :
      (realL2ExternalTensor oneL2 oneL2) p = oneL2 p.1 * oneL2 p.2 := by
    calc
      (realL2ExternalTensor oneL2 oneL2) p =
          realL2ExternalTensorFunction oneL2 oneL2 p := ht
      _ = oneL2 p.1 * oneL2 p.2 := rfl
  have h1' : oneL2 p.1 = 1 := by
    simpa [Function.comp_def] using h1
  have h2' : oneL2 p.2 = 1 := by
    simpa [Function.comp_def] using h2
  calc
    inner ℝ (K p) ((realL2ExternalTensor oneL2 oneL2) p) =
        inner ℝ
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta p.1 p.2)
          ((realL2ExternalTensor oneL2 oneL2) p) := by rw [hk]
    _ = inner ℝ
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta p.1 p.2)
          (oneL2 p.1 * oneL2 p.2) := by
      exact congrArg
        (fun z : ℝ => inner ℝ
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta p.1 p.2) z)
        ht'
    _ = periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta p.1 p.2 := by
      rw [h1', h2']
      simp [realL2Scalar_inner_eq_mul]

/-- The actual physical constant vector has strictly positive transfer expectation. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_transfer_expectation_pos
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 < inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N))
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) := by
  change 0 < inner ℝ
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
      H N hN beta hbeta
      (Lp.const 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) (1 : ℝ)))
    (Lp.const 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) (1 : ℝ))
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner]
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_const_one_eq_integral]
  exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pair_integral_pos
    H N hN beta hbeta

/-- The actual physical one-slab transfer is nonzero. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_ne_zero
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta ≠ 0 := by
  intro hzero
  have hpos := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_transfer_expectation_pos
    H N hN beta hbeta
  rw [hzero] at hpos
  simp at hpos

/-- The physical top transfer eigenvalue is strictly positive. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖ := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  have hT : T ≠ 0 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_ne_zero
      H N hN beta hbeta
  have hnorm_ne : ‖T‖ ≠ 0 := by
    intro hnorm
    exact hT (ContinuousLinearMap.opNorm_zero_iff.mp hnorm)
  exact lt_of_le_of_ne (norm_nonneg T) (Ne.symm hnorm_ne)

/-- The normalized actual physical one-slab transfer. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹ •
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta

@[simp] theorem periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_apply
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta f =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta f := rfl

/-- The chosen top eigenvector is fixed by the normalized transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_vacuum_fixed
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H N hN beta hbeta := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H N hN beta hbeta
  have hnorm_ne : ‖T‖ ≠ 0 :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H N hN beta hbeta).ne'
  have heig : T Ω = ‖T‖ • Ω :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_eigen H N hN beta hbeta
  change ‖T‖⁻¹ • T Ω = Ω
  rw [heig, smul_smul, inv_mul_cancel₀ hnorm_ne, one_smul]

/-- The normalized physical transfer has norm one. -/
theorem periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_norm
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖ = 1 := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H N hN beta hbeta
  have hnorm : 0 < ‖T‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos H N hN beta hbeta
  have hΩnorm : ‖Ω‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm H N hN beta hbeta
  have hΩfixed : S Ω = Ω :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_vacuum_fixed
      H N hN beta hbeta
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound S zero_le_one
    intro f
    change ‖‖T‖⁻¹ • T f‖ ≤ 1 * ‖f‖
    rw [one_mul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hnorm]
    rw [inv_mul_eq_div]
    exact (div_le_iff₀ hnorm).2 (by
      simpa [mul_comm] using ContinuousLinearMap.le_opNorm T f)
  · have hle := ContinuousLinearMap.le_opNorm S Ω
    rw [hΩfixed, hΩnorm] at hle
    simpa using hle

/-- Symmetry survives normalization. -/
theorem periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsSymmetric := by
  let c := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta‖⁻¹
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta
  have hT := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isSymmetric
    H N hN beta hbeta
  intro f g
  change inner ℝ (c • T f) g = inner ℝ f (c • T g)
  have h := congrArg (fun z : ℝ => c * z) (hT f g)
  simpa [inner_smul_left, inner_smul_right] using h

/-- Vacuum-orthogonal physical excitation sector. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationSubmodule
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Submodule ℝ (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (ℝ ∙ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H N hN beta hbeta)ᗮ

local instance periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitation_normedSpace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationSubmodule
        H N hN beta hbeta) :=
  Submodule.normedSpace _

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationSubmodule_mem
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    f ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationSubmodule H N hN beta hbeta ↔
      inner ℝ (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
        H N hN beta hbeta) f = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right

/-- The excitation sector is closed. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationSubmodule_isClosed
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsClosed
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationSubmodule
        H N hN beta hbeta :
        Submodule ℝ
          (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)) :
        Set (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationSubmodule
  exact (ℝ ∙ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
    H N hN beta hbeta).isClosed_orthogonal

/-- The normalized transfer preserves the excitation sector. -/
theorem periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_preserves_excitation
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N}
    (hf : f ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationSubmodule
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta f ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationSubmodule
        H N hN beta hbeta := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationSubmodule_mem] at hf ⊢
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H N hN beta hbeta
  have hS := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
    H N hN beta hbeta
  have hΩ : S Ω = Ω :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_vacuum_fixed
      H N hN beta hbeta
  calc
    inner ℝ Ω (S f) = inner ℝ (S Ω) f := (hS Ω f).symm
    _ = inner ℝ Ω f := by rw [hΩ]
    _ = 0 := hf

/-- The normalized transfer restricted to the physical excitation sector. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationTransferOperator
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationSubmodule
        H N hN beta hbeta →L[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationSubmodule
        H N hN beta hbeta :=
  ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta).comp
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationSubmodule
      H N hN beta hbeta).subtypeL).codRestrict
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationSubmodule H N hN beta hbeta)
      (fun f => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_preserves_excitation
        H N hN beta hbeta f.property)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationTransferOperator_coe
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationSubmodule
      H N hN beta hbeta) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationTransferOperator
      H N hN beta hbeta f :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationSubmodule
          H N hN beta hbeta) :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) =
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta f := rfl

/-- The excitation restriction is a contraction. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationTransferOperator_norm_le_one
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationTransferOperator
      H N hN beta hbeta‖ ≤ 1 := by
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  apply ContinuousLinearMap.opNorm_le_bound
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationTransferOperator
      H N hN beta hbeta) zero_le_one
  intro f
  change ‖S (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)‖ ≤
    1 * ‖f‖
  rw [one_mul]
  have h := ContinuousLinearMap.le_opNorm S
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
  rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_norm
    H N hN beta hbeta, one_mul] at h
  exact h

/-- Audit-visible normalization/excitation receipt. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNormalizationPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  physicalNormPositive : 0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖
  normalizedNorm : ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖ = 1
  vacuumFixed : periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H N hN beta hbeta) =
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector H N hN beta hbeta
  excitationNormLeOne : ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationTransferOperator
    H N hN beta hbeta‖ ≤ 1

/-- Construct the normalization/excitation package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNormalizationPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNormalizationPackage
      H N hN beta hbeta :=
  { physicalNormPositive := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H N hN beta hbeta
    normalizedNorm := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_norm
      H N hN beta hbeta
    vacuumFixed := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_vacuum_fixed
      H N hN beta hbeta
    excitationNormLeOne := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabExcitationTransferOperator_norm_le_one
      H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
