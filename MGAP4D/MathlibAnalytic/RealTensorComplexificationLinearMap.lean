import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Algebraic complexification of a real module by scalar extension.

This is deliberately the uncompleted tensor product.  It supplies the functorial
algebraic layer needed before introducing a Hilbert norm and completion. -/
namespace RealTensorComplexification

abbrev Space (E : Type*) [AddCommMonoid E] [Module ℝ E] :=
  ℂ ⊗[ℝ] E

/-- Extend a real-linear map to a complex-linear map on algebraic
complexifications. -/
def ofLinearMap
    {E F : Type*}
    [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid F] [Module ℝ F]
    (T : E →ₗ[ℝ] F) :
    Space E →ₗ[ℂ] Space F :=
  TensorProduct.AlgebraTensorModule.lTensor ℂ ℂ T

@[simp] theorem ofLinearMap_tmul
    {E F : Type*}
    [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid F] [Module ℝ F]
    (T : E →ₗ[ℝ] F)
    (z : ℂ)
    (x : E) :
    ofLinearMap T (z ⊗ₜ[ℝ] x) = z ⊗ₜ[ℝ] T x :=
  rfl

@[simp] theorem ofLinearMap_id
    {E : Type*}
    [AddCommMonoid E] [Module ℝ E] :
    ofLinearMap (LinearMap.id : E →ₗ[ℝ] E) =
      (LinearMap.id : Space E →ₗ[ℂ] Space E) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro z x
  rfl

@[simp] theorem ofLinearMap_zero
    {E F : Type*}
    [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid F] [Module ℝ F] :
    ofLinearMap (0 : E →ₗ[ℝ] F) =
      (0 : Space E →ₗ[ℂ] Space F) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro z x
  simp

@[simp] theorem ofLinearMap_add
    {E F : Type*}
    [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid F] [Module ℝ F]
    (S T : E →ₗ[ℝ] F) :
    ofLinearMap (S + T) = ofLinearMap S + ofLinearMap T := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro z x
  simp

/-- Scalar extension preserves composition. -/
theorem ofLinearMap_comp
    {E F G : Type*}
    [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid F] [Module ℝ F]
    [AddCommMonoid G] [Module ℝ G]
    (S : F →ₗ[ℝ] G)
    (T : E →ₗ[ℝ] F) :
    ofLinearMap (S.comp T) =
      (ofLinearMap S).comp (ofLinearMap T) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro z x
  rfl

/-- Forget continuity, then extend scalars algebraically. -/
def ofContinuousLinearMap
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) :
    Space E →ₗ[ℂ] Space F :=
  ofLinearMap T.toLinearMap

@[simp] theorem ofContinuousLinearMap_tmul
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F)
    (z : ℂ)
    (x : E) :
    ofContinuousLinearMap T (z ⊗ₜ[ℝ] x) =
      z ⊗ₜ[ℝ] T x :=
  rfl

@[simp] theorem ofContinuousLinearMap_one
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ofContinuousLinearMap (1 : E →L[ℝ] E) =
      (1 : Space E →ₗ[ℂ] Space E) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro z x
  rfl

@[simp] theorem ofContinuousLinearMap_zero
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ofContinuousLinearMap (0 : E →L[ℝ] F) =
      (0 : Space E →ₗ[ℂ] Space F) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro z x
  simp

/-- Algebraic scalar extension preserves composition of bounded real
operators. -/
theorem ofContinuousLinearMap_comp
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (S : F →L[ℝ] G)
    (T : E →L[ℝ] F) :
    ofContinuousLinearMap (S.comp T) =
      (ofContinuousLinearMap S).comp
        (ofContinuousLinearMap T) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro z x
  rfl

end RealTensorComplexification

end

end MathlibAnalytic
end MGAP4D
