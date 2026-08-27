import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open RCLike Real
open scoped InnerProductSpace ComplexConjugate TensorProduct

noncomputable section

universe u₁ u₂ u₃ u₄ u₅

variable {𝕜 : Type u₁} [RCLike 𝕜]
variable {E : Type u₂} {F : Type u₃} {G : Type u₄} {H : Type u₅}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The operator-norm inequality lifted to finite Gram matrices.  This is the
finite-dimensional estimate needed to make tensoring by a bounded operator
continuous for Mathlib's native Hilbert tensor norm. -/
theorem hilbertTensorPosSemidefOpNormSmulGramSubGram
    {n : Type*}
    (v : n → E)
    (f : E →L[𝕜] F) :
    (‖f‖ ^ 2 • Matrix.gram 𝕜 v - Matrix.gram 𝕜 (f ∘ v)).PosSemidef := by
  refine ⟨(Matrix.isHermitian_gram 𝕜 v).smul
      (((Pi.isSelfAdjoint.mpr (congrFun rfl)).apply f).pow 2)
    |>.sub (Matrix.isHermitian_gram 𝕜 (f ∘ v)), fun c ↦ ?_⟩
  simp_rw [Finsupp.sum, Matrix.sub_apply, Matrix.smul_apply, mul_sub, sub_mul,
    Finset.sum_sub_distrib, sub_nonneg]
  calc
    ∑ x ∈ c.support, ∑ y ∈ c.support,
        star (c x) * Matrix.gram 𝕜 (f ∘ v) x y * c y
      = (‖f (∑ x ∈ c.support, c x • v x)‖ : 𝕜) ^ 2 := by
          rw [Finset.sum_comm]
          simp [← inner_self_eq_norm_sq_to_K, inner_sum, sum_inner, inner_smul_left,
            inner_smul_right, Finset.mul_sum, Finset.smul_sum,
            RCLike.real_smul_eq_coe_mul]
          grind
    _ ≤ ‖f‖ ^ 2 • (‖∑ i ∈ c.support, c i • v i‖ : 𝕜) ^ 2 := by
      norm_cast
      grw [f.le_opNorm _, smul_eq_mul, ← mul_pow]
    _ = ∑ x ∈ c.support, ∑ y ∈ c.support,
        star (c x) * ‖f‖ ^ 2 • Matrix.gram 𝕜 v x y * c y := by
          rw [Finset.sum_comm]
          simp [← inner_self_eq_norm_sq_to_K, inner_sum, sum_inner, inner_smul_left,
            inner_smul_right, Finset.mul_sum, Finset.smul_sum,
            RCLike.real_smul_eq_coe_mul]
          grind

/-- Tensor a continuous linear map on the right by the identity, using the
native Hilbert tensor norm.  This is the project-local counterpart of the
later Mathlib `ContinuousLinearMap.rTensor` API. -/
noncomputable def hilbertTensorRTensor
    (f : E →L[𝕜] F)
    (G : Type u₄)
    [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] :
    (E ⊗[𝕜] G) →L[𝕜] (F ⊗[𝕜] G) :=
  (f.toLinearMap.rTensor G).mkContinuous ‖f‖ fun x ↦ by
    obtain ⟨n, e, g, hx⟩ := TensorProduct.exists_sum_tmul_eq x
    obtain ⟨c, hc_supp, hc⟩ := Submodule.mem_span_set.mp
      ((TensorProduct.span_tmul_eq_top 𝕜 E G) ▸ Submodule.mem_top (x := x))
    obtain ⟨m, A, hA⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp
      (hilbertTensorPosSemidefOpNormSmulGramSubGram e f)
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    simp_rw [sub_eq_iff_eq_add', ← sub_eq_iff_eq_add, ← Matrix.ext_iff,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.gram_apply, Function.comp_apply] at hA
    simp_rw [mul_pow, hx, map_sum, LinearMap.rTensor_tmul, ContinuousLinearMap.coe_coe,
      ← inner_self_eq_norm_sq (𝕜 := 𝕜), inner_sum, sum_inner, TensorProduct.inner_tmul,
      ← hA, sub_mul, Finset.sum_sub_distrib, map_sub, ← RCLike.smul_re,
      Finset.smul_sum, smul_mul_assoc, sub_le_self_iff, Matrix.sum_apply, mul_comm,
      Finset.mul_sum]
    simp_rw +singlePass [Finset.sum_comm_cycle, Matrix.vecMulVec, Matrix.of_apply,
      Pi.star_apply, ← mul_left_comm, ← mul_assoc, ← starRingEnd_self_apply (A _ _),
      ← inner_smul_left]
    simp [mul_comm, ← inner_smul_right, ← sum_inner, ← inner_sum, Finset.sum_nonneg]

@[simp] theorem hilbertTensorRTensor_apply
    (f : E →L[𝕜] F)
    (x : E ⊗[𝕜] G) :
    hilbertTensorRTensor f G x = f.toLinearMap.rTensor G x :=
  rfl

@[simp] theorem hilbertTensorRTensor_tmul
    (f : E →L[𝕜] F)
    (x : E)
    (y : G) :
    hilbertTensorRTensor f G (x ⊗ₜ[𝕜] y) = f x ⊗ₜ[𝕜] y :=
  rfl

/-- Tensoring on the right does not increase operator norm. -/
theorem hilbertTensorRTensor_norm_le
    (f : E →L[𝕜] F) :
    ‖hilbertTensorRTensor f G‖ ≤ ‖f‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

/-- Tensor a continuous linear map on the left by the identity. -/
noncomputable def hilbertTensorLTensor
    (g : G →L[𝕜] H)
    (E : Type u₂)
    [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] :
    (E ⊗[𝕜] G) →L[𝕜] (E ⊗[𝕜] H) :=
  TensorProduct.commIsometry 𝕜 H E ∘L
    hilbertTensorRTensor g E ∘L
      TensorProduct.commIsometry 𝕜 E G

@[simp] theorem hilbertTensorLTensor_apply
    (g : G →L[𝕜] H)
    (x : E ⊗[𝕜] G) :
    hilbertTensorLTensor g E x = g.toLinearMap.lTensor E x := by
  simp [hilbertTensorLTensor, ← LinearMap.comm_comp_rTensor_comp_comm_eq]

@[simp] theorem hilbertTensorLTensor_tmul
    (g : G →L[𝕜] H)
    (x : E)
    (y : G) :
    hilbertTensorLTensor g E (x ⊗ₜ[𝕜] y) = x ⊗ₜ[𝕜] g y :=
  rfl

/-- Tensoring on the left does not increase operator norm. -/
theorem hilbertTensorLTensor_norm_le
    (g : G →L[𝕜] H) :
    ‖hilbertTensorLTensor g E‖ ≤ ‖g‖ := by
  simp_rw [hilbertTensorLTensor,
    ← LinearIsometryEquiv.toContinuousLinearMap_toLinearIsometry]
  grw [ContinuousLinearMap.opNorm_comp_le, ContinuousLinearMap.opNorm_comp_le,
    LinearIsometry.norm_toContinuousLinearMap_le,
    LinearIsometry.norm_toContinuousLinearMap_le,
    mul_one, one_mul, hilbertTensorRTensor_norm_le]

/-- The continuous tensor product of two bounded operators, implemented on the
pinned Mathlib version where `TensorProduct.mapL` is not yet available. -/
noncomputable def hilbertTensorMap
    (f : E →L[𝕜] F)
    (g : G →L[𝕜] H) :
    (E ⊗[𝕜] G) →L[𝕜] (F ⊗[𝕜] H) :=
  hilbertTensorRTensor f H ∘L hilbertTensorLTensor g E

@[simp] theorem hilbertTensorMap_apply
    (f : E →L[𝕜] F)
    (g : G →L[𝕜] H)
    (x : E ⊗[𝕜] G) :
    hilbertTensorMap f g x = TensorProduct.map f.toLinearMap g.toLinearMap x := by
  simp [hilbertTensorMap, ← LinearMap.rTensor_comp_lTensor]

@[simp] theorem hilbertTensorMap_tmul
    (f : E →L[𝕜] F)
    (g : G →L[𝕜] H)
    (x : E)
    (y : G) :
    hilbertTensorMap f g (x ⊗ₜ[𝕜] y) = f x ⊗ₜ[𝕜] g y :=
  rfl

/-- The operator norm of the continuous tensor map is bounded by the product
of the factor operator norms. -/
theorem hilbertTensorMap_norm_le
    (f : E →L[𝕜] F)
    (g : G →L[𝕜] H) :
    ‖hilbertTensorMap f g‖ ≤ ‖f‖ * ‖g‖ := by
  calc
    ‖hilbertTensorMap f g‖ ≤
        ‖hilbertTensorRTensor f H‖ * ‖hilbertTensorLTensor g E‖ := by
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖f‖ * ‖g‖ := by
      exact mul_le_mul
        (hilbertTensorRTensor_norm_le (G := H) f)
        (hilbertTensorLTensor_norm_le (E := E) g)
        (norm_nonneg _)
        (norm_nonneg _)

end

end MathlibAnalytic
end MGAP4D
