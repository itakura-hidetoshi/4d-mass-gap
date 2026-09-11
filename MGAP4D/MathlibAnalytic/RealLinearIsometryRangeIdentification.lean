import MGAP4D.MathlibAnalytic.RealHilbertLinearIsometricOperatorTransport
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A linear isometry is a genuine isometric equivalence onto its algebraic
range.  Keeping the codomain as the range subtype avoids silently upgrading an
embedding to a surjective map onto the whole ambient Hilbert space. -/
noncomputable def realLinearIsometryEquivRange
    {E F : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    (f : E →ₗᵢ[ℝ] F) :
    E ≃ₗᵢ[ℝ] LinearMap.range f.toLinearMap := by
  let r : E →ₗ[ℝ] LinearMap.range f.toLinearMap :=
    f.toLinearMap.rangeRestrict
  have hr_injective : Function.Injective r := by
    intro x y hxy
    apply f.injective
    exact congrArg Subtype.val hxy
  have hr_surjective : Function.Surjective r := by
    intro y
    rcases y.property with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx
  let e : E ≃ₗ[ℝ] LinearMap.range f.toLinearMap :=
    LinearEquiv.ofBijective r ⟨hr_injective, hr_surjective⟩
  exact
    { toLinearEquiv := e
      norm_map' := by
        intro x
        change ‖f x‖ = ‖x‖
        exact f.norm_map x }

@[simp] theorem realLinearIsometryEquivRange_apply
    {E F : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    (f : E →ₗᵢ[ℝ] F)
    (x : E) :
    ((realLinearIsometryEquivRange f x :
        LinearMap.range f.toLinearMap) : F) = f x :=
  rfl

/-- Proof-relevant two-sided Hilbert identification between a source and the
exact range of one linear isometry. -/
noncomputable def realHilbertLinearIsometricIdentificationRange
    {E F : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    (f : E →ₗᵢ[ℝ] F) :
    RealHilbertLinearIsometricIdentification
      E (LinearMap.range f.toLinearMap) :=
  let e := realLinearIsometryEquivRange f
  { forward := e.toLinearIsometry
    inverse := e.symm.toLinearIsometry
    forward_inverse := e.apply_symm_apply
    inverse_forward := e.symm_apply_apply }

@[simp] theorem realHilbertLinearIsometricIdentificationRange_forward_coe
    {E F : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [NormedAddCommGroup F]
    [InnerProductSpace ℝ F]
    (f : E →ₗᵢ[ℝ] F)
    (x : E) :
    (((realHilbertLinearIsometricIdentificationRange f).forward x :
        LinearMap.range f.toLinearMap) : F) = f x := by
  exact realLinearIsometryEquivRange_apply f x

end

end MathlibAnalytic
end MGAP4D
