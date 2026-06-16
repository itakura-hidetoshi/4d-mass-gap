import Mathlib.Analysis.InnerProductSpace.Positive

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Adding a positive interaction to an operator with a quadratic-form lower
bound preserves the same lower bound. -/
theorem quadratic_form_lower_bound_add_of_isPositive
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {H₀ V : E →ₗ[ℝ] E}
    (δ : ℝ)
    (hFreeLower : ∀ x : E, δ * ‖x‖ ^ 2 ≤ inner ℝ (H₀ x) x)
    (hInteractionPositive : V.IsPositive)
    (x : E) :
    δ * ‖x‖ ^ 2 ≤ inner ℝ ((H₀ + V) x) x := by
  calc
    δ * ‖x‖ ^ 2 ≤ inner ℝ (H₀ x) x := hFreeLower x
    _ ≤ inner ℝ (H₀ x) x + inner ℝ (V x) x :=
      le_add_of_nonneg_right (hInteractionPositive.inner_nonneg_left x)
    _ = inner ℝ ((H₀ + V) x) x := by
      simp only [LinearMap.add_apply, inner_add_left]

/-- A symmetric free Hamiltonian plus a positive interaction is symmetric. -/
theorem isSymmetric_add_of_isPositive
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {H₀ V : E →ₗ[ℝ] E}
    (hFreeSymmetric : H₀.IsSymmetric)
    (hInteractionPositive : V.IsPositive) :
    (H₀ + V).IsSymmetric :=
  hFreeSymmetric.add hInteractionPositive.isSymmetric

end

end MathlibAnalytic
end MGAP4D
