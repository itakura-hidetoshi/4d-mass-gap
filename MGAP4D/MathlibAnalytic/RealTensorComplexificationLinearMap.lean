import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/- Algebraic complexification of a real module by scalar extension.

This is deliberately the uncompleted tensor product.  It supplies the functorial
algebraic layer needed before introducing a Hilbert norm and completion. -/
namespace RealTensorComplexification

universe u v w

abbrev Space (E : Type u) [AddCommMonoid E] [Module ℝ E] :=
  TensorProduct ℝ ℂ E

/-- Extend a real-linear map to a complex-linear map on algebraic
complexifications. -/
def ofLinearMap
    {E : Type u} {F : Type v}
    [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid F] [Module ℝ F]
    (T : E →ₗ[ℝ] F) :
    Space E →ₗ[ℂ] Space F :=
  T.baseChange ℂ

@[simp] theorem ofLinearMap_tmul
    {E : Type u} {F : Type v}
    [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid F] [Module ℝ F]
    (T : E →ₗ[ℝ] F)
    (z : ℂ)
    (x : E) :
    ofLinearMap T (z ⊗ₜ[ℝ] x) = z ⊗ₜ[ℝ] T x :=
  LinearMap.baseChange_tmul T z x

@[simp] theorem ofLinearMap_id
    {E : Type u}
    [AddCommMonoid E] [Module ℝ E] :
    ofLinearMap (LinearMap.id : E →ₗ[ℝ] E) =
      (LinearMap.id : Space E →ₗ[ℂ] Space E) :=
  LinearMap.baseChange_id

@[simp] theorem ofLinearMap_zero
    {E : Type u} {F : Type v}
    [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid F] [Module ℝ F] :
    ofLinearMap (0 : E →ₗ[ℝ] F) =
      (0 : Space E →ₗ[ℂ] Space F) :=
  LinearMap.baseChange_zero

@[simp] theorem ofLinearMap_add
    {E : Type u} {F : Type v}
    [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid F] [Module ℝ F]
    (S T : E →ₗ[ℝ] F) :
    ofLinearMap (S + T) = ofLinearMap S + ofLinearMap T :=
  LinearMap.baseChange_add S T

/-- Scalar extension preserves composition. -/
theorem ofLinearMap_comp
    {E : Type u} {F : Type v} {G : Type w}
    [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid F] [Module ℝ F]
    [AddCommMonoid G] [Module ℝ G]
    (S : F →ₗ[ℝ] G)
    (T : E →ₗ[ℝ] F) :
    ofLinearMap (S.comp T) =
      (ofLinearMap S).comp (ofLinearMap T) :=
  LinearMap.baseChange_comp T S

/-- Forget continuity, then extend scalars algebraically. -/
def ofContinuousLinearMap
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) :
    Space E →ₗ[ℂ] Space F :=
  ofLinearMap T.toLinearMap

@[simp] theorem ofContinuousLinearMap_tmul
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F)
    (z : ℂ)
    (x : E) :
    ofContinuousLinearMap T (z ⊗ₜ[ℝ] x) =
      z ⊗ₜ[ℝ] T x :=
  ofLinearMap_tmul T.toLinearMap z x

@[simp] theorem ofContinuousLinearMap_one
    {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ofContinuousLinearMap (1 : E →L[ℝ] E) =
      (1 : Space E →ₗ[ℂ] Space E) := by
  simpa [ofContinuousLinearMap] using (ofLinearMap_id (E := E))

@[simp] theorem ofContinuousLinearMap_zero
    {E : Type u} {F : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ofContinuousLinearMap (0 : E →L[ℝ] F) =
      (0 : Space E →ₗ[ℂ] Space F) := by
  simpa [ofContinuousLinearMap] using (ofLinearMap_zero (E := E) (F := F))

/-- Algebraic scalar extension preserves composition of bounded real
operators. -/
theorem ofContinuousLinearMap_comp
    {E : Type u} {F : Type v} {G : Type w}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (S : F →L[ℝ] G)
    (T : E →L[ℝ] F) :
    ofContinuousLinearMap (S.comp T) =
      (ofContinuousLinearMap S).comp
        (ofContinuousLinearMap T) := by
  simpa [ofContinuousLinearMap] using
    (ofLinearMap_comp S.toLinearMap T.toLinearMap)

end RealTensorComplexification

end

end MathlibAnalytic
end MGAP4D
