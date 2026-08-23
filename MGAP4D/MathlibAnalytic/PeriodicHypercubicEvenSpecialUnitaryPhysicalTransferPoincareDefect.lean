import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceExponentialDecay
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferFactorization
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

/-- For a symmetric compact operator with nonnegative quadratic form, every
global quadratic-defect coefficient `δ ≤ 1` forces `‖R‖ ≤ 1 - δ`.
Together with the preceding theorem, this identifies `1 - ‖R‖` as the optimal
Poincare coefficient. The symmetry input is stated as an explicit real pairing
identity so concrete subtype transports never have to elaborate a scalar-
polymorphic `IsSymmetric` proposition. -/
theorem realHilbertSymmetricCompact_opNorm_le_one_sub_of_quadraticDefect
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (R : E →L[ℝ] E)
    (hSymm : ∀ f g : E, inner ℝ (R f) g = inner ℝ f (R g))
    (hNonneg : ∀ f : E, 0 ≤ inner ℝ (R f) f)
    (hCompact : IsCompactOperator R)
    {δ : ℝ}
    (hδle : δ ≤ 1)
    (hdefect : ∀ f : E,
      δ * ‖f‖ ^ 2 ≤ realHilbertQuadraticDefect R f) :
    ‖R‖ ≤ 1 - δ := by
  have hPositive : (R : E →ₗ[ℝ] E).IsPositive := by
    refine ⟨?_, ?_⟩
    · intro f g
      exact hSymm f g
    · intro f
      simpa using hNonneg f
  by_cases hRzero : R = 0
  · rw [hRzero, norm_zero]
    linarith
  · have hex : ∃ u : E, R u ≠ 0 := by
      by_contra h
      push Not at h
      apply hRzero
      apply ContinuousLinearMap.ext
      intro u
      simpa using h u
    obtain ⟨u, huR⟩ := hex
    have hu : u ≠ 0 := by
      intro hu0
      apply huR
      rw [hu0, map_zero]
    let unit : E := ‖u‖⁻¹ • u
    have hunorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hunit : ‖unit‖ = 1 := by
      dsimp [unit]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hunorm_pos]
      exact inv_mul_cancel₀ hunorm_pos.ne'
    obtain ⟨v, hvnorm, hveig⟩ :=
      realHilbertPositiveCompact_exists_unit_topEigenvector
        R unit hunit hPositive hCompact
    have hinner : inner ℝ (R v) v = ‖R‖ := by
      rw [hveig]
      simp [inner_smul_left, hvnorm]
    have hvdefect := hdefect v
    dsimp [realHilbertQuadraticDefect] at hvdefect
    rw [hinner, hvnorm] at hvdefect
    norm_num at hvdefect
    linarith

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

local instance periodicHypercubicEvenSpecialUnitaryPhysicalPoincare_completeSpace
    (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

local instance periodicHypercubicEvenSpecialUnitaryPhysicalTopEigenspaceOrthogonal_completeSpace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
    H N hN beta hbeta).isClosed_orthogonal.completeSpace_coe

/-- Conversely, every Poincare coefficient on the actual orthogonal sector is
bounded above by the canonical transfer gap. The proof stays on the already
instanced concrete excitation carrier and transports the real pairing symmetry,
quadratic positivity and compactness from the ambient normalized physical
transfer. -/
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
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta
  have hRpair : ∀ f g :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta,
      inner ℝ (R f) g = inner ℝ f (R g) := by
    intro f g
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
  have hRnonneg : ∀ f :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta,
      0 ≤ inner ℝ (R f) f := by
    intro f
    change 0 ≤ inner ℝ
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta
        (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
      (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    exact
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isPositive
        H N hN beta hbeta).inner_nonneg_left _
  have hRcompact : IsCompactOperator R := by
    simpa [R,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator] using
      (realHilbertTopEigenspaceOrthogonalRestriction_isCompact
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isCompact
          H N hN beta hbeta))
  have hR : ‖R‖ ≤ 1 - δ :=
    realHilbertSymmetricCompact_opNorm_le_one_sub_of_quadraticDefect
      R hRpair hRnonneg hRcompact hδle (by
        intro f
        simpa [R,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceQuadraticDefect]
          using hdefect f)
  dsimp [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap, R]
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