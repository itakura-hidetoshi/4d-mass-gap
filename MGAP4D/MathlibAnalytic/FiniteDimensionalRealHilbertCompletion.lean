import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Extend

namespace MGAP4D
namespace MathlibAnalytic

open Function

noncomputable section

/-- A finite-dimensional real Hilbert space is canonically linearly isometric
to its uniform completion.  We orient the equivalence from the completion back
to the original space because this is the direction needed to transport finite
dimensionality through the completed tensor carriers used by
`RealHilbertKernelFeature.pow`.

The construction uses only the pinned Mathlib completion API: extend the
identity linear equivalence along the dense canonical embedding into the
completion and the identity embedding into the already complete
finite-dimensional space. -/
noncomputable def finiteDimensionalRealHilbertCompletionLinearIsometryEquiv
    (E : Type*)
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    UniformSpace.Completion E ≃ₗᵢ[ℝ] E := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let e₁ : E →ₗ[ℝ] UniformSpace.Completion E :=
    (UniformSpace.Completion.toComplL :
      E →L[ℝ] UniformSpace.Completion E).toLinearMap
  let e₂ : E →ₗ[ℝ] E := LinearMap.id
  refine (LinearEquiv.refl ℝ E).extendOfIsometry e₁ e₂ ?_ ?_ ?_
  · simpa [e₁] using
      (UniformSpace.Completion.denseRange_coe (α := E))
  · simpa [e₂] using (denseRange_id : DenseRange (id : E → E))
  · intro x
    simp [e₁, e₂]

/-- On the canonical dense copy of a finite-dimensional Hilbert space, the
completion equivalence is exactly the identity. -/
@[simp] theorem finiteDimensionalRealHilbertCompletionLinearIsometryEquiv_coe
    (E : Type*)
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (x : E) :
    finiteDimensionalRealHilbertCompletionLinearIsometryEquiv E
        (x : UniformSpace.Completion E) = x := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  unfold finiteDimensionalRealHilbertCompletionLinearIsometryEquiv
  rw [show (x : UniformSpace.Completion E) =
      ((UniformSpace.Completion.toComplL :
        E →L[ℝ] UniformSpace.Completion E).toLinearMap x) by rfl]
  rw [LinearEquiv.extendOfIsometry_eq]
  rfl

/-- Conversely, the inverse equivalence is the canonical completion embedding. -/
@[simp] theorem finiteDimensionalRealHilbertCompletionLinearIsometryEquiv_symm_apply
    (E : Type*)
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (x : E) :
    (finiteDimensionalRealHilbertCompletionLinearIsometryEquiv E).symm x =
      (x : UniformSpace.Completion E) := by
  apply (finiteDimensionalRealHilbertCompletionLinearIsometryEquiv E).injective
  simp

/-- The uniform completion of a finite-dimensional real Hilbert space is again
finite-dimensional.  This theorem is intentionally not registered globally as
an instance; downstream recursive tensor constructions install it locally at
the exact carrier where it is needed. -/
theorem finiteDimensional_realHilbert_completion
    (E : Type*)
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    FiniteDimensional ℝ (UniformSpace.Completion E) := by
  exact
    (finiteDimensionalRealHilbertCompletionLinearIsometryEquiv E).symm.toLinearEquiv.finiteDimensional

end

end MathlibAnalytic
end MGAP4D
