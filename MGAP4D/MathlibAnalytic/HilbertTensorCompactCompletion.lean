import MGAP4D.MathlibAnalytic.ContinuousLinearMapCompletionFunctor
import MGAP4D.MathlibAnalytic.HilbertTensorContinuousMap
import MGAP4D.MathlibAnalytic.RealHilbertCompactFiniteDimensionalApproximation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Function Set
open scoped TensorProduct InnerProductSpace

noncomputable section

universe u₁ u₂ u₃

/-- Tensoring respects composition for the project-local continuous Hilbert
tensor map.  This is the functorial identity needed to factor finite-rank
tensor approximants through a finite-dimensional tensor square. -/
theorem hilbertTensorMap_comp
    {E₀ E₁ E₂ F₀ F₁ F₂ : Type*}
    [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
    [NormedAddCommGroup F₀] [InnerProductSpace ℝ F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁]
    [NormedAddCommGroup F₂] [InnerProductSpace ℝ F₂]
    (f₁ : E₀ →L[ℝ] E₁) (f₂ : E₁ →L[ℝ] E₂)
    (g₁ : F₀ →L[ℝ] F₁) (g₂ : F₁ →L[ℝ] F₂) :
    hilbertTensorMap (f₂ ∘L f₁) (g₂ ∘L g₁) =
      hilbertTensorMap f₂ g₂ ∘L hilbertTensorMap f₁ g₁ := by
  apply ContinuousLinearMap.ext
  intro x
  simpa only [hilbertTensorMap_apply, ContinuousLinearMap.comp_apply] using
    (TensorProduct.map_map
      f₂.toLinearMap g₂.toLinearMap f₁.toLinearMap g₁.toLinearMap x).symm

/-- Difference identity for tensor squares.  It is the operator analogue of
`A⊗A - B⊗B = (A-B)⊗A + B⊗(A-B)`. -/
theorem hilbertTensorMap_self_sub_self
    {E : Type u₁}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A B : E →L[ℝ] E) :
    hilbertTensorMap A A - hilbertTensorMap B B =
      hilbertTensorMap (A - B) A + hilbertTensorMap B (A - B) := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
        hilbertTensorMap_tmul]
      rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add,
        TensorProduct.neg_tmul, TensorProduct.tmul_neg]
      abel
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy]

/-- Operator-norm Lipschitz estimate for tensor squares. -/
theorem hilbertTensorMap_self_sub_self_norm_le
    {E : Type u₁}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A B : E →L[ℝ] E) :
    ‖hilbertTensorMap A A - hilbertTensorMap B B‖ ≤
      ‖A - B‖ * ‖A‖ + ‖B‖ * ‖A - B‖ := by
  rw [hilbertTensorMap_self_sub_self]
  calc
    ‖hilbertTensorMap (A - B) A + hilbertTensorMap B (A - B)‖ ≤
        ‖hilbertTensorMap (A - B) A‖ + ‖hilbertTensorMap B (A - B)‖ :=
      ContinuousLinearMap.opNorm_add_le _ _
    _ ≤ ‖A - B‖ * ‖A‖ + ‖B‖ * ‖A - B‖ :=
      add_le_add
        (hilbertTensorMap_norm_le (A - B) A)
        (hilbertTensorMap_norm_le B (A - B))

/-- Passing two bounded maps to canonical uniform completions does not enlarge
the norm of their difference.  This dense-copy estimate avoids needing a
separate additivity API for `ContinuousLinearMap.completion`. -/
theorem continuousLinearMap_completion_sub_opNorm_le
    {E F : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [NormedAddCommGroup F]
    [NormedSpace ℝ F]
    (f g : E →L[ℝ] F) :
    ‖f.completion - g.completion‖ ≤ ‖f - g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact norm_nonneg (f - g)
  · intro x
    refine UniformSpace.Completion.induction_on x ?_ ?_
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · intro a
      simpa only [ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.completion_apply_coe,
          ← UniformSpace.Completion.coe_sub,
          UniformSpace.Completion.norm_coe] using
        (f - g).le_opNorm a

/-- The completion of the tensor square of a map factoring through a
finite-dimensional Hilbert subspace is compact.  Instead of completing the
finite-dimensional intermediate carrier and then cancelling that completion,
we extend the incoming tensor map directly along the canonical dense embedding
into the completed source.  The intermediate tensor square remains literally
finite-dimensional and hence locally compact. -/
theorem realHilbertFiniteDimensionalFactor_tensorSquareCompletion_isCompact
    {E : Type u₁}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (V : Submodule ℝ E)
    [FiniteDimensional ℝ V]
    (B : E →L[ℝ] V) :
    IsCompactOperator
      ((hilbertTensorMap (V.subtypeL ∘L B) (V.subtypeL ∘L B)).completion) := by
  let X := E ⊗[ℝ] E
  let W := V ⊗[ℝ] V
  letI : FiniteDimensional ℝ W := by
    dsimp [W]
    infer_instance
  letI : IsBoundedSMul ℝ W :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ) (E := W)
  letI : UniformContinuousConstSMul ℝ W := by infer_instance
  letI : ContinuousConstSMul ℝ W := by infer_instance
  let e : X →L[ℝ] UniformSpace.Completion X :=
    (UniformSpace.Completion.toComplL :
      X →L[ℝ] UniformSpace.Completion X)
  have he_dense : DenseRange e := by
    simpa [e] using
      (UniformSpace.Completion.denseRange_coe (α := X))
  have he_uniform : IsUniformInducing e := by
    simpa [e] using
      (UniformSpace.Completion.isUniformInducing_coe X)
  let C₀ : X →L[ℝ] W := hilbertTensorMap B B
  let D₀ : W →L[ℝ] X := hilbertTensorMap V.subtypeL V.subtypeL
  let C : UniformSpace.Completion X →L[ℝ] W := C₀.extend e
  let D : W →L[ℝ] UniformSpace.Completion X :=
    (UniformSpace.Completion.toComplL :
        X →L[ℝ] UniformSpace.Completion X) ∘L D₀
  have hC : IsCompactOperator C :=
    isCompactOperator_of_locallyCompactSpace_dom C
  have hDC : IsCompactOperator (D ∘L C) := hC.clm_comp D
  have hfactor :
      D ∘L C =
        (hilbertTensorMap (V.subtypeL ∘L B) (V.subtypeL ∘L B)).completion := by
    apply ContinuousLinearMap.ext
    intro x
    refine UniformSpace.Completion.induction_on x ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro a
      calc
        (D ∘L C) (a : UniformSpace.Completion X) =
            (D₀ (C₀ a) : UniformSpace.Completion X) := by
          simp only [D, C, ContinuousLinearMap.comp_apply,
            UniformSpace.Completion.coe_toComplL]
          rw [show (a : UniformSpace.Completion X) = e a by rfl]
          rw [ContinuousLinearMap.extend_eq C₀ he_dense he_uniform a]
        _ =
            (hilbertTensorMap (V.subtypeL ∘L B) (V.subtypeL ∘L B) a :
              UniformSpace.Completion X) := by
          congr 1
          exact
            (DFunLike.congr_fun
              (hilbertTensorMap_comp B V.subtypeL B V.subtypeL) a).symm
        _ =
            (hilbertTensorMap (V.subtypeL ∘L B) (V.subtypeL ∘L B)).completion
              (a : UniformSpace.Completion X) := by
          rw [ContinuousLinearMap.completion_apply_coe]
  rw [← hfactor]
  exact hDC

/-- A compact bounded operator on a complete real Hilbert space has compact
completed Hilbert tensor square.  Compactness is proved by the canonical
finite-dimensional approximation from `RealHilbertCompactFiniteDimensionalApproximation`,
then closure of compact operators in operator norm. -/
theorem realHilbertCompact_tensorSquareCompletion_isCompact
    {E : Type u₁}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →L[ℝ] E)
    (hA : IsCompactOperator A) :
    IsCompactOperator ((hilbertTensorMap A A).completion) := by
  change
    (hilbertTensorMap A A).completion ∈
      {T : UniformSpace.Completion (E ⊗[ℝ] E) →L[ℝ]
          UniformSpace.Completion (E ⊗[ℝ] E) | IsCompactOperator T}
  rw [← isClosed_setOf_isCompactOperator.closure_eq]
  refine Metric.mem_closure_iff.2 ?_
  intro ε hε
  let c : ℝ := 2 * ‖A‖ + 1
  have hc : 0 < c := by
    dsimp [c]
    nlinarith [norm_nonneg A]
  let δ : ℝ := min 1 (ε / c)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min zero_lt_one (div_pos hε hc)
  obtain ⟨V, hV, B, hApprox⟩ :=
    realHilbertCompact_exists_finiteDimensional_factor_approx A hA hδ
  letI : FiniteDimensional ℝ V := hV
  let F : E →L[ℝ] E := V.subtypeL ∘L B
  let Q : (E ⊗[ℝ] E) →L[ℝ] (E ⊗[ℝ] E) := hilbertTensorMap F F
  have hAF : ‖A - F‖ < δ := by
    simpa [F] using hApprox
  have hδ_one : δ ≤ 1 := by
    exact min_le_left _ _
  have hAF_one : ‖A - F‖ ≤ 1 := by
    exact (le_of_lt hAF).trans hδ_one
  have hF_norm : ‖F‖ ≤ ‖A‖ + 1 := by
    have hF_eq : F = A - (A - F) := by abel
    rw [hF_eq]
    exact (norm_sub_le A (A - F)).trans
      (add_le_add_right hAF_one ‖A‖)
  have hTensor :
      ‖hilbertTensorMap A A - Q‖ ≤ ‖A - F‖ * c := by
    calc
      ‖hilbertTensorMap A A - Q‖ =
          ‖hilbertTensorMap A A - hilbertTensorMap F F‖ := by rfl
      _ ≤ ‖A - F‖ * ‖A‖ + ‖F‖ * ‖A - F‖ :=
        hilbertTensorMap_self_sub_self_norm_le A F
      _ ≤ ‖A - F‖ * ‖A‖ + (‖A‖ + 1) * ‖A - F‖ := by
        exact add_le_add_right
          (mul_le_mul_of_nonneg_right hF_norm (norm_nonneg (A - F))) _
      _ = ‖A - F‖ * c := by
        dsimp [c]
        ring
  have hδ_c : δ * c ≤ ε := by
    have hmin : δ ≤ ε / c := min_le_right _ _
    calc
      δ * c ≤ (ε / c) * c := mul_le_mul_of_nonneg_right hmin hc.le
      _ = ε := by field_simp
  have hTensor_lt : ‖hilbertTensorMap A A - Q‖ < ε := by
    calc
      ‖hilbertTensorMap A A - Q‖ ≤ ‖A - F‖ * c := hTensor
      _ < δ * c := mul_lt_mul_of_pos_right hAF hc
      _ ≤ ε := hδ_c
  have hCompletion :
      ‖(hilbertTensorMap A A).completion - Q.completion‖ < ε := by
    exact (continuousLinearMap_completion_sub_opNorm_le
      (hilbertTensorMap A A) Q).trans_lt hTensor_lt
  have hQCompact : IsCompactOperator Q.completion := by
    simpa [Q, F] using
      realHilbertFiniteDimensionalFactor_tensorSquareCompletion_isCompact V B
  refine ⟨Q.completion, hQCompact, ?_⟩
  simpa [dist_eq_norm, norm_sub_rev] using hCompletion

end

end MathlibAnalytic
end MGAP4D