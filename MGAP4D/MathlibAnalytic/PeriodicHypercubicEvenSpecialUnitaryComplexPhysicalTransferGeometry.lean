import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransfer
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

/-- The genuine real physical carrier embeds linearly and isometrically in the
same-root complex Gauss-law Hilbert space. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOfRealLinearIsometry
    (H N : ℕ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N where
  toFun := periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N
  map_add' := periodicHypercubicEvenSpecialUnitaryPhysicalOfReal_add H N
  map_smul' := periodicHypercubicEvenSpecialUnitaryPhysicalOfReal_smul H N
  norm_map' := periodicHypercubicEvenSpecialUnitaryPhysicalOfReal_norm H N

/-- The physical real-part operation, bundled over the restricted real scalar
structure of the genuine complex carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPartCLM
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  LinearMap.mkContinuous
    { toFun := periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N
      map_add' := periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart_add H N
      map_smul' := by
        intro c f
        simpa using
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart_smul
            H N (c : ℂ) f) }
    1
    (by
      intro f
      simpa using
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart_norm_le H N f)

/-- The physical imaginary-part operation, bundled over the restricted real
scalar structure of the genuine complex carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPartCLM
    (H N : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N :=
  LinearMap.mkContinuous
    { toFun := periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N
      map_add' := periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart_add H N
      map_smul' := by
        intro c f
        simpa using
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart_smul
            H N (c : ℂ) f) }
    1
    (by
      intro f
      simpa using
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart_norm_le H N f)

/-- Every genuine complex physical vector is reconstructed from its physical
real and imaginary components inside the same Gauss-law sector. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysical_reconstruct
    (H N : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f) +
      Complex.I • periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f) = f := by
  apply periodicHypercubicEvenSpecialUnitaryComplexPhysical_ext_components H N
  · simp [periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart_smul]
  · simp [periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart_smul]

/-- The real physical embedding preserves the Hilbert pairing, with the real
pairing canonically viewed in `ℂ`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOfReal_inner
    (H N : ℕ)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    inner ℂ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N f)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N g) =
      (inner ℝ f g : ℂ) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  change inner ℂ
      (periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal H N
        (f : Lp ℝ 2 μ))
      (periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal H N
        (g : Lp ℝ 2 μ)) =
    (inner ℝ (f : Lp ℝ 2 μ) (g : Lp ℝ 2 μ) : ℂ)
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def, ← integral_complex_ofReal]
  apply integral_congr_ae
  have hf := periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal_coeFn
    H N (f : Lp ℝ 2 μ)
  have hg := periodicHypercubicEvenSpecialUnitarySpatialSliceRealL2OfReal_coeFn
    H N (g : Lp ℝ 2 μ)
  filter_upwards [hf, hg] with A hfA hgA
  rw [hfA, hgA]
  simp [RCLike.inner_apply]

/-- Exact decomposition of the genuine complex physical inner product into
real physical components. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysical_inner_components
    (H N : ℕ)
    (f g : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    inner ℂ f g =
      (inner ℝ
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f)
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N g) : ℂ) +
      (inner ℝ
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f)
          (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N g) : ℂ) +
      Complex.I *
        ((inner ℝ
            (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f)
            (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N g) : ℂ) -
          (inner ℝ
            (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f)
            (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N g) : ℂ)) := by
  rw [← periodicHypercubicEvenSpecialUnitaryComplexPhysical_reconstruct H N f,
    ← periodicHypercubicEvenSpecialUnitaryComplexPhysical_reconstruct H N g]
  simp [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    periodicHypercubicEvenSpecialUnitaryPhysicalOfReal_inner]
  ring

/-- Pythagoras for the genuine complex Gauss-law Hilbert space. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysical_norm_sq
    (H N : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    ‖f‖ ^ 2 =
      ‖periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f‖ ^ 2 +
      ‖periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f‖ ^ 2 := by
  rw [← norm_sq_eq_re_inner (𝕜 := ℂ) f,
    periodicHypercubicEvenSpecialUnitaryComplexPhysical_inner_components]
  simp [real_inner_self_eq_norm_sq]

/-- The scalar extension obeys the exact operator-norm pointwise estimate; no
factor two is lost. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_norm_le
    (H N : ℕ)
    (T : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N T f‖ ≤
      ‖T‖ * ‖f‖ := by
  let xr := periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f
  let xi := periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f
  let TC := periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N T
  have hIn : ‖f‖ ^ 2 = ‖xr‖ ^ 2 + ‖xi‖ ^ 2 := by
    simpa [xr, xi] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysical_norm_sq H N f
  have hOut : ‖TC f‖ ^ 2 = ‖T xr‖ ^ 2 + ‖T xi‖ ^ 2 := by
    simpa [TC, xr, xi] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysical_norm_sq H N (TC f)
  have hr := ContinuousLinearMap.le_opNorm T xr
  have hi := ContinuousLinearMap.le_opNorm T xi
  have hr2 : ‖T xr‖ ^ 2 ≤ (‖T‖ * ‖xr‖) ^ 2 := by
    nlinarith [norm_nonneg (T xr), norm_nonneg T, norm_nonneg xr]
  have hi2 : ‖T xi‖ ^ 2 ≤ (‖T‖ * ‖xi‖) ^ 2 := by
    nlinarith [norm_nonneg (T xi), norm_nonneg T, norm_nonneg xi]
  have hsq : ‖TC f‖ ^ 2 ≤ (‖T‖ * ‖f‖) ^ 2 := by
    rw [hOut]
    nlinarith [hIn, hr2, hi2, sq_nonneg ‖T‖]
  change ‖TC f‖ ≤ ‖T‖ * ‖f‖
  nlinarith [hsq, norm_nonneg (TC f), norm_nonneg T, norm_nonneg f,
    mul_nonneg (norm_nonneg T) (norm_nonneg f)]

/-- Canonical scalar extension preserves the operator norm exactly. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_norm
    (H N : ℕ)
    (T : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N T‖ = ‖T‖ := by
  let TC := periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N T
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound TC (norm_nonneg T)
    intro f
    simpa [TC] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_norm_le H N T f
  · apply ContinuousLinearMap.opNorm_le_bound T (norm_nonneg TC)
    intro f
    calc
      ‖T f‖ = ‖periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N (T f)‖ :=
        (periodicHypercubicEvenSpecialUnitaryPhysicalOfReal_norm H N (T f)).symm
      _ = ‖TC (periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N f)‖ := by
        rw [TC,
          periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_ofReal]
      _ ≤ ‖TC‖ * ‖periodicHypercubicEvenSpecialUnitaryPhysicalOfReal H N f‖ :=
        ContinuousLinearMap.le_opNorm TC _
      _ = ‖TC‖ * ‖f‖ := by
        rw [periodicHypercubicEvenSpecialUnitaryPhysicalOfReal_norm]

/-- Symmetry is preserved by the canonical scalar extension. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_isSymmetric
    (H N : ℕ)
    (T : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (hT : (T :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsSymmetric) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N T :
        PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
          PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
      PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →ₗ[ℂ]
        PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N).IsSymmetric := by
  intro f g
  rw [periodicHypercubicEvenSpecialUnitaryComplexPhysical_inner_components H N
      (periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N T f) g,
    periodicHypercubicEvenSpecialUnitaryComplexPhysical_inner_components H N f
      (periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N T g)]
  simp only [periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexificationFun_realPart,
    periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexificationFun_imagPart]
  rw [hT
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f)
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N g),
    hT
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f)
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N g),
    hT
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f)
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N g),
    hT
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f)
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N g)]

/-- Positivity is preserved by the canonical scalar extension. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_isPositive
    (H N : ℕ)
    (T : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (hT : (T :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsPositive) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N T :
        PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
          PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
      PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →ₗ[ℂ]
        PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N).IsPositive := by
  refine ⟨periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_isSymmetric
    H N T hT.isSymmetric, ?_⟩
  intro f
  rw [periodicHypercubicEvenSpecialUnitaryComplexPhysical_inner_components H N
      (periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N T f) f]
  simp only [periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexificationFun_realPart,
    periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexificationFun_imagPart]
  have hre := hT.re_inner_nonneg_left
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPart H N f)
  have him := hT.re_inner_nonneg_left
    (periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPart H N f)
  simpa using add_nonneg hre him

/-- Compactness is preserved by the same canonical scalar extension. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_isCompact
    (H N : ℕ)
    (T : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (hT : IsCompactOperator T) :
    IsCompactOperator
      (periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N T) := by
  let reL := periodicHypercubicEvenSpecialUnitaryComplexPhysicalRealPartCLM H N
  let imL := periodicHypercubicEvenSpecialUnitaryComplexPhysicalImagPartCLM H N
  let emb :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOfRealLinearIsometry H N).toContinuousLinearMap
  have hre0 : IsCompactOperator (T ∘ reL) := hT.comp_clm reL
  have hre : IsCompactOperator (emb ∘ (T ∘ reL)) := hre0.clm_comp emb
  have him0 : IsCompactOperator (T ∘ imL) := hT.comp_clm imL
  have himBase : IsCompactOperator (emb ∘ (T ∘ imL)) := him0.clm_comp emb
  have him : IsCompactOperator (Complex.I • (emb ∘ (T ∘ imL))) :=
    himBase.smul Complex.I
  have hadd := hre.add him
  simpa [Function.comp_def, reL, imL, emb,
    periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexificationFun] using hadd

local instance periodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferGeometryCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

/-- The genuine complex normalized finite Wilson transfer has exactly the real
operator norm. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_norm
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖ = 1 := by
  rw [periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator,
    periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_norm]
  exact periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_norm
    H N hN beta hbeta

/-- The normalized finite Wilson transfer is positive on the genuine complex
physical Hilbert space. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_isPositive
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta :
        PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
          PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
      PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →ₗ[ℂ]
        PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N).IsPositive := by
  exact periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_isPositive
    H N
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isPositive
      H N hN beta hbeta)

/-- Hence the genuine complex normalized transfer is symmetric. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_isSymmetric
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta :
        PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
          PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
      PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →ₗ[ℂ]
        PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N).IsSymmetric :=
  (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_isPositive
    H N hN beta hbeta).isSymmetric

/-- In the complete genuine complex physical Hilbert space, symmetry is the
usual bounded self-adjointness statement. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_isSelfAdjoint
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsSelfAdjoint
      (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  exact
    (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H N hN beta hbeta).clm_adjoint_eq

/-- The normalized finite Wilson transfer remains compact after exact scalar
extension to the genuine complex physical carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_isCompact
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsCompactOperator
      (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta) := by
  exact periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_isCompact
    H N
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isCompact
      H N hN beta hbeta)

end
end MathlibAnalytic
end MGAP4D
