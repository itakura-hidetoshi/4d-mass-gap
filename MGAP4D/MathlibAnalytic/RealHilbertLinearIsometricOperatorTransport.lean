import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- A proof-relevant identification of two real Hilbert carriers by mutually
inverse linear isometries.  Keeping both directions explicit avoids silently
promoting an arbitrary embedding to a surjective equivalence. -/
structure RealHilbertLinearIsometricIdentification
    (E F : Type*)
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] where
  forward : E →ₗᵢ[ℝ] F
  inverse : F →ₗᵢ[ℝ] E
  forward_inverse : ∀ y : F, forward (inverse y) = y
  inverse_forward : ∀ x : E, inverse (forward x) = x

namespace RealHilbertLinearIsometricIdentification

variable
    {E F : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    (I : RealHilbertLinearIsometricIdentification E F)

/-- Conjugate a bounded operator through a genuine real-linear isometric
identification. -/
noncomputable def transportOperator
    (A : E →L[ℝ] E) : F →L[ℝ] F :=
  I.forward.toContinuousLinearMap.comp
    (A.comp I.inverse.toContinuousLinearMap)

@[simp] theorem transportOperator_apply
    (A : E →L[ℝ] E)
    (y : F) :
    I.transportOperator A y = I.forward (A (I.inverse y)) :=
  rfl

/-- Exact source-to-target intertwining for the transported operator. -/
@[simp] theorem transportOperator_apply_forward
    (A : E →L[ℝ] E)
    (x : E) :
    I.transportOperator A (I.forward x) = I.forward (A x) := by
  rw [I.transportOperator_apply, I.inverse_forward]

/-- The forward identification preserves the real inner product. -/
@[simp] theorem forward_inner
    (x y : E) :
    inner ℝ (I.forward x) (I.forward y) = inner ℝ x y :=
  LinearIsometry.inner_map_map I.forward x y

/-- The inverse identification preserves the real inner product. -/
@[simp] theorem inverse_inner
    (x y : F) :
    inner ℝ (I.inverse x) (I.inverse y) = inner ℝ x y :=
  LinearIsometry.inner_map_map I.inverse x y

/-- Symmetry is invariant under isometric conjugation. -/
theorem transportOperator_isSymmetric
    (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) :
    (I.transportOperator A).toLinearMap.IsSymmetric := by
  intro y z
  calc
    inner ℝ (I.transportOperator A y) z =
        inner ℝ
          (I.forward (A (I.inverse y)))
          (I.forward (I.inverse z)) := by
      rw [I.transportOperator_apply, I.forward_inverse]
    _ = inner ℝ (A (I.inverse y)) (I.inverse z) :=
      I.forward_inner _ _
    _ = inner ℝ (I.inverse y) (A (I.inverse z)) :=
      hA _ _
    _ = inner ℝ
          (I.forward (I.inverse y))
          (I.forward (A (I.inverse z))) :=
      (I.forward_inner _ _).symm
    _ = inner ℝ y (I.transportOperator A z) := by
      rw [I.forward_inverse, I.transportOperator_apply]

/-- A pointwise operator bound is preserved exactly by isometric conjugation. -/
theorem transportOperator_norm_le
    (A : E →L[ℝ] E)
    (bound : ℝ)
    (hA : ∀ x : E, ‖A x‖ ≤ bound * ‖x‖)
    (y : F) :
    ‖I.transportOperator A y‖ ≤ bound * ‖y‖ := by
  rw [I.transportOperator_apply, I.forward.norm_map,
    ← I.inverse.norm_map y]
  exact hA (I.inverse y)

/-- The transported operator has operator norm bounded by any common
pointwise source bound. -/
theorem transportOperator_opNorm_le
    (A : E →L[ℝ] E)
    (bound : ℝ)
    (hbound : 0 ≤ bound)
    (hA : ∀ x : E, ‖A x‖ ≤ bound * ‖x‖) :
    ‖I.transportOperator A‖ ≤ bound := by
  exact ContinuousLinearMap.opNorm_le_bound _ hbound
    (I.transportOperator_norm_le A bound hA)

/-- Every quadratic lower bound is transported with the same exact constant. -/
theorem transportOperator_quadratic_lower_bound
    (A : E →L[ℝ] E)
    (c : ℝ)
    (hA : ∀ x : E, c * ‖x‖ ^ 2 ≤ inner ℝ (A x) x)
    (y : F) :
    c * ‖y‖ ^ 2 ≤ inner ℝ (I.transportOperator A y) y := by
  let x : E := I.inverse y
  have hy : I.forward x = y := I.forward_inverse y
  calc
    c * ‖y‖ ^ 2 = c * ‖x‖ ^ 2 := by
      rw [← hy, I.forward.norm_map]
    _ ≤ inner ℝ (A x) x := hA x
    _ = inner ℝ (I.forward (A x)) (I.forward x) :=
      (I.forward_inner _ _).symm
    _ = inner ℝ (I.transportOperator A y) y := by
      rw [← hy, I.transportOperator_apply_forward]

/-- The transported operator is uniquely characterized by its exact
intertwining with the forward identification. -/
theorem transportOperator_unique
    (A : E →L[ℝ] E)
    (B : F →L[ℝ] F)
    (hB : ∀ x : E, B (I.forward x) = I.forward (A x)) :
    I.transportOperator A = B := by
  ext y
  calc
    I.transportOperator A y =
        I.transportOperator A (I.forward (I.inverse y)) := by
      rw [I.forward_inverse]
    _ = I.forward (A (I.inverse y)) :=
      I.transportOperator_apply_forward A (I.inverse y)
    _ = B (I.forward (I.inverse y)) :=
      (hB (I.inverse y)).symm
    _ = B y := by rw [I.forward_inverse]

end RealHilbertLinearIsometricIdentification

/-- Audit-visible receipt for an operator and all properties transported
through a genuine real-Hilbert linear-isometric identification. -/
structure RealHilbertLinearIsometricOperatorTransportPackage
    (E F : Type*)
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] where
  identification : RealHilbertLinearIsometricIdentification E F
  sourceOperator : E →L[ℝ] E
  targetOperator : F →L[ℝ] F
  exactIntertwining :
    ∀ x : E,
      targetOperator (identification.forward x) =
        identification.forward (sourceOperator x)
  uniqueTransport :
    targetOperator = identification.transportOperator sourceOperator

/-- Construct the generic audit receipt from one source operator and one
isometric carrier identification. -/
noncomputable def realHilbertLinearIsometricOperatorTransportPackage
    (E F : Type*)
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    (I : RealHilbertLinearIsometricIdentification E F)
    (A : E →L[ℝ] E) :
    RealHilbertLinearIsometricOperatorTransportPackage E F where
  identification := I
  sourceOperator := A
  targetOperator := I.transportOperator A
  exactIntertwining := I.transportOperator_apply_forward A
  uniqueTransport := rfl

end

end MathlibAnalytic
end MGAP4D
