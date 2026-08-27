import MGAP4D.MathlibAnalytic.HilbertTensorContinuousMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped TensorProduct InnerProductSpace

noncomputable section

universe u₁ u₂ u₃ u₄

variable {E : Type u₁} {F : Type u₂} {G : Type u₃} {H : Type u₄}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Tensoring two real linear isometries preserves the full native Hilbert
inner product on the algebraic tensor product.  This is the isometric analogue
of the bounded `hilbertTensorMap` construction and is proved directly from the
universal tensor-product inner product. -/
theorem hilbertTensorLinearIsometry_inner
    (f : E →ₗᵢ[ℝ] F)
    (g : G →ₗᵢ[ℝ] H)
    (x y : E ⊗[ℝ] G) :
    inner ℝ
        (TensorProduct.map f.toLinearMap g.toLinearMap x)
        (TensorProduct.map f.toLinearMap g.toLinearMap y) =
      inner ℝ x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e k =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul e' k' =>
          simp [TensorProduct.inner_tmul]
      | add y₁ y₂ hy₁ hy₂ =>
          rw [map_add, inner_add_right, inner_add_right, hy₁, hy₂]
  | add x₁ x₂ hx₁ hx₂ =>
      rw [map_add, inner_add_left, inner_add_left, hx₁, hx₂]

/-- The tensor product of two real linear isometries, bundled as a linear
isometry for Mathlib's native algebraic Hilbert-tensor norm. -/
noncomputable def hilbertTensorLinearIsometry
    (f : E →ₗᵢ[ℝ] F)
    (g : G →ₗᵢ[ℝ] H) :
    (E ⊗[ℝ] G) →ₗᵢ[ℝ] (F ⊗[ℝ] H) :=
  (TensorProduct.map f.toLinearMap g.toLinearMap).isometryOfInner
    (hilbertTensorLinearIsometry_inner f g)

@[simp] theorem hilbertTensorLinearIsometry_apply
    (f : E →ₗᵢ[ℝ] F)
    (g : G →ₗᵢ[ℝ] H)
    (x : E ⊗[ℝ] G) :
    hilbertTensorLinearIsometry f g x =
      TensorProduct.map f.toLinearMap g.toLinearMap x :=
  rfl

@[simp] theorem hilbertTensorLinearIsometry_tmul
    (f : E →ₗᵢ[ℝ] F)
    (g : G →ₗᵢ[ℝ] H)
    (x : E)
    (y : G) :
    hilbertTensorLinearIsometry f g (x ⊗ₜ[ℝ] y) =
      f x ⊗ₜ[ℝ] g y := by
  rfl

/-- Explicit norm receipt for the tensor product of two linear isometries. -/
theorem hilbertTensorLinearIsometry_norm
    (f : E →ₗᵢ[ℝ] F)
    (g : G →ₗᵢ[ℝ] H)
    (x : E ⊗[ℝ] G) :
    ‖hilbertTensorLinearIsometry f g x‖ = ‖x‖ :=
  (hilbertTensorLinearIsometry f g).norm_map x

end

end MathlibAnalytic
end MGAP4D
