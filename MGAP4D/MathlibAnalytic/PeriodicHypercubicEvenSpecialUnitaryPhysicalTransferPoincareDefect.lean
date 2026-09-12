import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceExponentialDecay
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferFactorization
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Module End
open scoped InnerProductSpace InnerProduct

noncomputable section

universe u

/-- Quadratic Dirichlet defect of a bounded real Hilbert-space operator. -/
noncomputable def realHilbertQuadraticDefect
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (R : E →L[ℝ] E)
    (f : E) : ℝ :=
  ‖f‖ ^ 2 - inner ℝ (R f) f

/-- The operator-norm separation `1 - ‖R‖` always lower-bounds the quadratic
Dirichlet defect. No compactness or spectral theorem is needed in this
direction. -/
theorem realHilbert_one_sub_opNorm_mul_norm_sq_le_quadraticDefect
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (R : E →L[ℝ] E)
    (f : E) :
    (1 - ‖R‖) * ‖f‖ ^ 2 ≤ realHilbertQuadraticDefect R f := by
  have hCS :
      |inner ℝ (R f) f| ≤ ‖R f‖ * ‖f‖ := by
    simpa [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) (R f) f)
  have hOp : ‖R f‖ ≤ ‖R‖ * ‖f‖ :=
    ContinuousLinearMap.le_opNorm R f
  have hf0 : 0 ≤ ‖f‖ := norm_nonneg f
  have hinner : inner ℝ (R f) f ≤ ‖R‖ * ‖f‖ ^ 2 := by
    calc
      inner ℝ (R f) f ≤ |inner ℝ (R f) f| := le_abs_self _
      _ ≤ ‖R f‖ * ‖f‖ := hCS
      _ ≤ (‖R‖ * ‖f‖) * ‖f‖ :=
        mul_le_mul_of_nonneg_right hOp hf0
      _ = ‖R‖ * ‖f‖ ^ 2 := by ring
  dsimp [realHilbertQuadraticDefect]
  linarith

/-- For a symmetric operator with nonnegative quadratic form, every global
quadratic-defect coefficient `δ ≤ 1` forces `‖R‖ ≤ 1 - δ`.

This is stronger than the compact-operator converse originally needed here:
compactness and top-eigenvector attainment are unnecessary. Mathlib's exact
Rayleigh formula for the norm of a symmetric bounded operator reduces the
claim directly to the pointwise defect inequality. -/
theorem realHilbertSymmetric_opNorm_le_one_sub_of_quadraticDefect
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (R : E →L[ℝ] E)
    (hSymm : ∀ f g : E, inner ℝ (R f) g = inner ℝ f (R g))
    (hNonneg : ∀ f : E, 0 ≤ inner ℝ (R f) f)
    {δ : ℝ}
    (hδle : δ ≤ 1)
    (hdefect : ∀ f : E,
      δ * ‖f‖ ^ 2 ≤ realHilbertQuadraticDefect R f) :
    ‖R‖ ≤ 1 - δ := by
  have hSymmetric : (R : E →ₗ[ℝ] E).IsSymmetric := by
    intro f g
    exact hSymm f g
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient R hSymmetric]
  apply ciSup_le
  intro f
  by_cases hf : f = 0
  · subst f
    simpa using sub_nonneg.mpr hδle
  · have hnorm_pos : 0 < ‖f‖ := norm_pos_iff.mpr hf
    have hnorm_sq_pos : 0 < ‖f‖ ^ 2 := by positivity
    have hdef := hdefect f
    dsimp [realHilbertQuadraticDefect] at hdef
    have hinner : inner ℝ (R f) f ≤ (1 - δ) * ‖f‖ ^ 2 := by
      linarith
    have hq_nonneg : 0 ≤ R.rayleighQuotient f := by
      change 0 ≤ inner ℝ (R f) f / ‖f‖ ^ 2
      exact div_nonneg (hNonneg f) (sq_nonneg _)
    have hq_le : R.rayleighQuotient f ≤ 1 - δ := by
      change inner ℝ (R f) f / ‖f‖ ^ 2 ≤ 1 - δ
      exact (div_le_iff₀ hnorm_sq_pos).2 (by
        calc
          inner ℝ (R f) f ≤ (1 - δ) * ‖f‖ ^ 2 := hinner
          _ = (1 - δ) * ‖f‖ ^ 2 := rfl)
    rw [abs_of_nonneg hq_nonneg]
    exact hq_le

/-- Actual finite-volume Poincare/Dirichlet defect on the orthogonal complement
of the full eigenvalue-one space of the normalized physical one-slab transfer. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceQuadraticDefect
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) : ℝ :=
  realHilbertQuadraticDefect
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta) f

/-- The existing finite-volume transfer gap is a Poincare lower bound for the
actual top-eigenspace-orthogonal sector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap_mul_norm_sq_le_quadraticDefect
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta * ‖f‖ ^ 2 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceQuadraticDefect
        H N hN beta hbeta f := by
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceQuadraticDefect] using
    (realHilbert_one_sub_opNorm_mul_norm_sq_le_quadraticDefect
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta) f)

/-- Explicit real pairing symmetry of the normalized physical transfer after
restriction to the full top-eigenspace orthogonal sector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_inner_symm
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta f) g =
      inner ℝ f
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta g) := by
  change inner ℝ
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta
        (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
      (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) =
    inner ℝ
      (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta
        (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
  exact
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H N hN beta hbeta _ _

/-- The restricted normalized physical transfer has nonnegative quadratic
form, inherited from ambient transfer positivity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_inner_nonneg
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    0 ≤ inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta f) f := by
  change 0 ≤ inner ℝ
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta
      (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
  exact
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isPositive
      H N hN beta hbeta).inner_nonneg_left _

/-- Conversely, every Poincare coefficient on the actual orthogonal sector is
bounded above by the canonical transfer gap. Thus the canonical finite-volume
gap is exactly the optimal quadratic-defect coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspacePoincareCoefficient_le_transferGap
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {δ : ℝ}
    (hδle : δ ≤ 1)
    (hdefect : ∀ f :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta,
      δ * ‖f‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceQuadraticDefect
          H N hN beta hbeta f) :
    δ ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
      H N hN beta hbeta := by
  let K : Submodule ℝ
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
    (realHilbertTopEigenspace
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta))ᗮ
  letI hKNorm : NormedAddCommGroup K := inferInstance
  letI hKInner : InnerProductSpace ℝ K := Submodule.innerProductSpace K
  let R : K →L[ℝ] K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta
  have hSymm : ∀ f g : K, inner ℝ (R f) g = inner ℝ f (R g) := by
    intro f g
    simpa [K, R] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_inner_symm
        H N hN beta hbeta f g
  have hNonneg : ∀ f : K, 0 ≤ inner ℝ (R f) f := by
    intro f
    simpa [K, R] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_inner_nonneg
        H N hN beta hbeta f
  have hDefect : ∀ f : K, δ * ‖f‖ ^ 2 ≤ realHilbertQuadraticDefect R f := by
    intro f
    simpa [K, R,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceQuadraticDefect] using
      hdefect f
  have hR : ‖R‖ ≤ 1 - δ :=
    @realHilbertSymmetric_opNorm_le_one_sub_of_quadraticDefect
      K hKNorm hKInner R hSymm hNonneg δ hδle hDefect
  have hR' :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ ≤ 1 - δ := by
    simpa [R, K] using hR
  dsimp [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap]
  linarith

/-- The finite-volume transfer gap is at most one. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap_le_one
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
      H N hN beta hbeta ≤ 1 := by
  dsimp [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap]
  linarith [norm_nonneg
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta)]

/-- The same quadratic defect is exactly the loss of the actual Wilson
Moore--Aronszajn feature-analysis energy after normalization by the physical
transfer norm. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceQuadraticDefect_eq_featureAnalysis
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceQuadraticDefect
        H N hN beta hbeta f =
      ‖(f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)‖ ^ 2 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
            H N hN beta hbeta
            (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)‖ ^ 2 := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let A := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
    H N hN beta hbeta
  let x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N := f
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceQuadraticDefect
  unfold realHilbertQuadraticDefect
  change ‖x‖ ^ 2 -
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta x) x =
    ‖x‖ ^ 2 - ‖T‖⁻¹ * ‖A x‖ ^ 2
  have hquad : inner ℝ (T x) x = ‖A x‖ ^ 2 := by
    simpa [T, A] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_quadratic_eq_analysis_norm_sq
        H N hN beta hbeta x
  have hscaled :
      inner ℝ (‖T‖⁻¹ • T x) x = ‖T‖⁻¹ * ‖A x‖ ^ 2 := by
    have h := congrArg (fun z : ℝ => ‖T‖⁻¹ * z) hquad
    simpa [inner_smul_left] using h
  rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_apply]
  simpa [T, A] using hscaled

/-- Using `‖T_phys‖ = ‖A_phys‖²`, the preceding identity is expressed purely
in terms of the actual Wilson feature-analysis operator. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceQuadraticDefect_eq_normalizedFeatureAnalysis
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceQuadraticDefect
        H N hN beta hbeta f =
      ‖(f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)‖ ^ 2 -
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
          H N hN beta hbeta‖ ^ 2)⁻¹ *
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFeatureAnalysisOperator
            H N hN beta hbeta
            (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)‖ ^ 2 := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceQuadraticDefect_eq_featureAnalysis]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_eq_analysis_sq]

/-- The midpoint decay factor from #2040 is exactly one minus one half of the
canonical transfer gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor_eq_one_sub_half_transferGap
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
        H N hN beta hbeta =
      1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
          H N hN beta hbeta / 2 := by
  dsimp [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor,
    realStrictContractionMidpointFactor,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap]
  ring

/-- Therefore the canonical finite-volume logarithmic decay rate is the exact
monotone transform of the finite-volume Poincare/transfer gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_eq_neg_log_one_sub_half_transferGap
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta =
      -Real.log
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
            H N hN beta hbeta / 2) := by
  dsimp [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate,
    realStrictContractionMidpointRate,
    realStrictContractionMidpointFactor,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap]
  congr 2
  ring

end

end MathlibAnalytic
end MGAP4D