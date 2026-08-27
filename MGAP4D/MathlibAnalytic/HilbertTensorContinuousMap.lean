import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open RCLike Real
open scoped InnerProductSpace ComplexConjugate TensorProduct

noncomputable section

universe u₂ u₃ u₄ u₅

variable {E : Type u₂} {F : Type u₃} {G : Type u₄} {H : Type u₅}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The real operator-norm inequality lifted to finite Gram matrices.  This is
exactly the estimate needed for the physical real Hilbert spaces in the
excitation sector. -/
theorem hilbertTensorPosSemidefOpNormSmulGramSubGram
    {n : Type*}
    (v : n → E)
    (f : E →L[ℝ] F) :
    (‖f‖ ^ 2 • Matrix.gram ℝ v - Matrix.gram ℝ (f ∘ v)).PosSemidef := by
  refine ⟨(Matrix.isHermitian_gram ℝ v).smul
      (((Pi.isSelfAdjoint.mpr (congrFun rfl)).apply f).pow 2)
    |>.sub (Matrix.isHermitian_gram ℝ (f ∘ v)), fun c ↦ ?_⟩
  simp_rw [Finsupp.sum, Matrix.sub_apply, Matrix.smul_apply, mul_sub, sub_mul,
    Finset.sum_sub_distrib, sub_nonneg]
  calc
    ∑ x ∈ c.support, ∑ y ∈ c.support,
        star (c x) * Matrix.gram ℝ (f ∘ v) x y * c y
      = (‖f (∑ x ∈ c.support, c x • v x)‖ : ℝ) ^ 2 := by
          rw [← inner_self_eq_norm_sq (𝕜 := ℝ)]
          simp_rw [map_sum, map_smul, inner_sum, sum_inner, inner_smul_left,
            inner_smul_right]
          rw [Finset.sum_comm]
          simp [Matrix.gram_apply, Function.comp_apply, mul_comm, mul_left_comm]
    _ ≤ ‖f‖ ^ 2 • (‖∑ i ∈ c.support, c i • v i‖ : ℝ) ^ 2 := by
      norm_cast
      grw [f.le_opNorm _, smul_eq_mul, ← mul_pow]
    _ = ∑ x ∈ c.support, ∑ y ∈ c.support,
        star (c x) * ‖f‖ ^ 2 • Matrix.gram ℝ v x y * c y := by
          have hgram :
              (‖∑ i ∈ c.support, c i • v i‖ : ℝ) ^ 2 =
                ∑ x ∈ c.support, ∑ y ∈ c.support,
                  star (c x) * Matrix.gram ℝ v x y * c y := by
            rw [← inner_self_eq_norm_sq (𝕜 := ℝ)]
            simp_rw [inner_sum, sum_inner, inner_smul_left, inner_smul_right]
            rw [Finset.sum_comm]
            simp [Matrix.gram_apply, mul_comm, mul_left_comm]
          rw [hgram]
          simp only [smul_eq_mul]
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro y hy
          ring

/-- Pointwise boundedness of tensoring a real bounded operator by the identity
for Mathlib's native Hilbert tensor norm. -/
theorem hilbertTensorRTensor_bound
    (f : E →L[ℝ] F)
    (x : E ⊗[ℝ] G) :
    ‖f.toLinearMap.rTensor G x‖ ≤ ‖f‖ * ‖x‖ := by
  obtain ⟨n, e, g, hx⟩ := TensorProduct.exists_sum_tmul_eq x
  have hpsd :
      (‖f‖ ^ 2 • Matrix.gram ℝ e - Matrix.gram ℝ (f ∘ e)).PosSemidef :=
    hilbertTensorPosSemidefOpNormSmulGramSubGram e f
  obtain ⟨m, A, hA⟩ :=
    (Matrix.posSemidef_iff_eq_sum_vecMulVec (𝕜 := ℝ) (n := Fin n)).mp hpsd
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simp_rw [sub_eq_iff_eq_add', ← sub_eq_iff_eq_add, ← Matrix.ext_iff,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.gram_apply, Function.comp_apply] at hA
  simp_rw [mul_pow, hx, map_sum, LinearMap.rTensor_tmul, ContinuousLinearMap.coe_coe,
    ← inner_self_eq_norm_sq (𝕜 := ℝ), inner_sum, sum_inner, TensorProduct.inner_tmul,
    ← hA, sub_mul, Finset.sum_sub_distrib, map_sub, ← RCLike.smul_re,
    Finset.smul_sum, smul_mul_assoc, sub_le_self_iff, Matrix.sum_apply, mul_comm,
    Finset.mul_sum]
  simp_rw +singlePass [Finset.sum_comm_cycle, Matrix.vecMulVec, Matrix.of_apply,
    Pi.star_apply, ← mul_left_comm, ← mul_assoc, ← starRingEnd_self_apply (A _ _),
    ← inner_smul_left]
  simp [mul_comm, ← inner_smul_right, ← sum_inner, ← inner_sum, Finset.sum_nonneg]

/-- Tensor a continuous real linear map on the right by the identity, using the
native Hilbert tensor norm.  This is the project-local counterpart of the
later Mathlib `ContinuousLinearMap.rTensor` API. -/
noncomputable def hilbertTensorRTensor
    (f : E →L[ℝ] F)
    (G : Type u₄)
    [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] :
    (E ⊗[ℝ] G) →L[ℝ] (F ⊗[ℝ] G) :=
  (f.toLinearMap.rTensor G).mkContinuous ‖f‖ fun x ↦
    hilbertTensorRTensor_bound f x

@[simp] theorem hilbertTensorRTensor_apply
    (f : E →L[ℝ] F)
    (x : E ⊗[ℝ] G) :
    hilbertTensorRTensor f G x = f.toLinearMap.rTensor G x :=
  rfl

@[simp] theorem hilbertTensorRTensor_tmul
    (f : E →L[ℝ] F)
    (x : E)
    (y : G) :
    hilbertTensorRTensor f G (x ⊗ₜ[ℝ] y) = f x ⊗ₜ[ℝ] y :=
  rfl

/-- Tensoring on the right does not increase operator norm. -/
theorem hilbertTensorRTensor_norm_le
    (f : E →L[ℝ] F) :
    ‖hilbertTensorRTensor f G‖ ≤ ‖f‖ := by
  refine ContinuousLinearMap.opNorm_le_bound
    (hilbertTensorRTensor f G) (norm_nonneg f) ?_
  exact fun x => hilbertTensorRTensor_bound f x

/-- Tensor a continuous real linear map on the left by the identity. -/
noncomputable def hilbertTensorLTensor
    (g : G →L[ℝ] H)
    (E : Type u₂)
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] :
    (E ⊗[ℝ] G) →L[ℝ] (E ⊗[ℝ] H) :=
  TensorProduct.commIsometry ℝ H E ∘L
    hilbertTensorRTensor g E ∘L
      TensorProduct.commIsometry ℝ E G

@[simp] theorem hilbertTensorLTensor_apply
    (g : G →L[ℝ] H)
    (x : E ⊗[ℝ] G) :
    hilbertTensorLTensor g E x = g.toLinearMap.lTensor E x := by
  simp [hilbertTensorLTensor, ← LinearMap.comm_comp_rTensor_comp_comm_eq]

@[simp] theorem hilbertTensorLTensor_tmul
    (g : G →L[ℝ] H)
    (x : E)
    (y : G) :
    hilbertTensorLTensor g E (x ⊗ₜ[ℝ] y) = x ⊗ₜ[ℝ] g y :=
  rfl

/-- Tensoring on the left does not increase operator norm. -/
theorem hilbertTensorLTensor_norm_le
    (g : G →L[ℝ] H) :
    ‖hilbertTensorLTensor g E‖ ≤ ‖g‖ := by
  simp_rw [hilbertTensorLTensor,
    ← LinearIsometryEquiv.toContinuousLinearMap_toLinearIsometry]
  grw [ContinuousLinearMap.opNorm_comp_le, ContinuousLinearMap.opNorm_comp_le,
    LinearIsometry.norm_toContinuousLinearMap_le,
    LinearIsometry.norm_toContinuousLinearMap_le,
    mul_one, one_mul, hilbertTensorRTensor_norm_le]

/-- The continuous tensor product of two bounded real operators, implemented
on the pinned Mathlib version where `TensorProduct.mapL` is not yet available. -/
noncomputable def hilbertTensorMap
    (f : E →L[ℝ] F)
    (g : G →L[ℝ] H) :
    (E ⊗[ℝ] G) →L[ℝ] (F ⊗[ℝ] H) :=
  hilbertTensorRTensor f H ∘L hilbertTensorLTensor g E

@[simp] theorem hilbertTensorMap_apply
    (f : E →L[ℝ] F)
    (g : G →L[ℝ] H)
    (x : E ⊗[ℝ] G) :
    hilbertTensorMap f g x = TensorProduct.map f.toLinearMap g.toLinearMap x := by
  simp [hilbertTensorMap, ← LinearMap.rTensor_comp_lTensor]

@[simp] theorem hilbertTensorMap_tmul
    (f : E →L[ℝ] F)
    (g : G →L[ℝ] H)
    (x : E)
    (y : G) :
    hilbertTensorMap f g (x ⊗ₜ[ℝ] y) = f x ⊗ₜ[ℝ] g y :=
  rfl

/-- The operator norm of the continuous tensor map is bounded by the product
of the factor operator norms. -/
theorem hilbertTensorMap_norm_le
    (f : E →L[ℝ] F)
    (g : G →L[ℝ] H) :
    ‖hilbertTensorMap f g‖ ≤ ‖f‖ * ‖g‖ := by
  calc
    ‖hilbertTensorMap f g‖ ≤
        ‖hilbertTensorRTensor f H‖ * ‖hilbertTensorLTensor g E‖ := by
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖f‖ * ‖g‖ := by
      exact mul_le_mul
        (hilbertTensorRTensor_norm_le (G := H) f)
        (hilbertTensorLTensor_norm_le (E := E) g)
        (norm_nonneg (hilbertTensorLTensor g E))
        (norm_nonneg f)

/-- Pointwise product bound for the continuous tensor map. -/
theorem hilbertTensorMap_apply_norm_le
    (f : E →L[ℝ] F)
    (g : G →L[ℝ] H)
    (x : E ⊗[ℝ] G) :
    ‖hilbertTensorMap f g x‖ ≤ (‖f‖ * ‖g‖) * ‖x‖ := by
  calc
    ‖hilbertTensorMap f g x‖ ≤ ‖hilbertTensorMap f g‖ * ‖x‖ :=
      (hilbertTensorMap f g).le_opNorm x
    _ ≤ (‖f‖ * ‖g‖) * ‖x‖ :=
      mul_le_mul_of_nonneg_right (hilbertTensorMap_norm_le f g) (norm_nonneg x)

/-- Transport the tensor-product operator bound across an explicit equality of
continuous linear maps.  Concrete specializations can use this receipt without
unfolding their map definitions during the norm proof. -/
theorem hilbertTensorMap_opNorm_le_of_eq
    (A : (E ⊗[ℝ] G) →L[ℝ] (F ⊗[ℝ] H))
    (f : E →L[ℝ] F)
    (g : G →L[ℝ] H)
    (hA : A = hilbertTensorMap f g) :
    ContinuousLinearMap.opNorm A ≤ ‖f‖ * ‖g‖ := by
  rw [hA]
  exact hilbertTensorMap_norm_le f g

/-- For a bounded endomorphism, the tensor square is bounded by the square of
its operator norm.  The single map argument pins the exact Hilbert topology,
which is useful for concrete closed subspaces carrying inherited topologies. -/
theorem hilbertTensorMap_self_norm_le
    (f : E →L[ℝ] E) :
    ‖hilbertTensorMap (E := E) (F := E) (G := E) (H := E) f f‖ ≤
      ‖f‖ * ‖f‖ := by
  exact hilbertTensorMap_norm_le
    (E := E) (F := E) (G := E) (H := E) f f

end

end MathlibAnalytic
end MGAP4D
