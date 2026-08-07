import MGAP4D.MathlibAnalytic.FiniteUniformAverageComplementKernelCongruence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Uniform second moment of a finite slab decomposition
`left(x) + crossing(u,x,y) + right(y)`. -/
noncomputable def finiteUniformSlabSecondMoment
    {α γ : Type*} [Fintype γ]
    (left right : α → ℝ)
    (crossing : γ → α → α → ℝ)
    (x y : α) : ℝ :=
  (Fintype.card γ : ℝ)⁻¹ *
    ∑ u : γ, (left x + crossing u x y + right y) ^ 2

/-- Uniform second moment of the crossing part alone. -/
noncomputable def finiteUniformCrossingSecondMoment
    {α γ : Type*} [Fintype γ]
    (crossing : γ → α → α → ℝ)
    (x y : α) : ℝ :=
  (Fintype.card γ : ℝ)⁻¹ *
    ∑ u : γ, (crossing u x y) ^ 2

/-- The only genuinely two-boundary part forced by the square expansion before
projector correction: crossing second moment plus the spatial rank-one term. -/
noncomputable def finiteUniformSlabSecondMomentInteraction
    {α γ : Type*} [Fintype γ]
    (left right : α → ℝ)
    (crossing : γ → α → α → ℝ)
    (x y : α) : ℝ :=
  finiteUniformCrossingSecondMoment crossing x y +
    2 * left x * right y

/-- Exact pointwise square decomposition when the uniform crossing mean is one
boundary-independent scalar. -/
theorem finiteUniformSlabSecondMoment_eq_interaction_add_additive
    {α γ : Type*} [Fintype γ] [Nonempty γ]
    (left right : α → ℝ)
    (crossing : γ → α → α → ℝ)
    (crossingMean : ℝ)
    (hMean : ∀ x y : α,
      (Fintype.card γ : ℝ)⁻¹ * ∑ u : γ, crossing u x y = crossingMean)
    (x y : α) :
    finiteUniformSlabSecondMoment
        (α := α) (γ := γ) left right crossing x y =
      finiteUniformSlabSecondMomentInteraction
          (α := α) (γ := γ) left right crossing x y +
        (left x) ^ 2 + (right y) ^ 2 +
        2 * crossingMean * left x + 2 * crossingMean * right y := by
  classical
  let n : ℝ := Fintype.card γ
  have hn : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card γ ≠ 0)
  let l := left x
  let r := right y
  let c : γ → ℝ := fun u => crossing u x y
  have hmean : n⁻¹ * ∑ u : γ, c u = crossingMean := by
    simpa [n, c] using hMean x y
  unfold finiteUniformSlabSecondMoment
    finiteUniformSlabSecondMomentInteraction
    finiteUniformCrossingSecondMoment
  change
    n⁻¹ * ∑ u : γ, (l + c u + r) ^ 2 =
      n⁻¹ * ∑ u : γ, (c u) ^ 2 + 2 * l * r +
        l ^ 2 + r ^ 2 + 2 * crossingMean * l + 2 * crossingMean * r
  have hpoint : ∀ u : γ,
      (l + c u + r) ^ 2 =
        (c u) ^ 2 +
          (2 * l) * c u + (2 * r) * c u +
          (l ^ 2 + r ^ 2 + 2 * l * r) := by
    intro u
    ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have hconst' :
      n⁻¹ * ∑ _u : γ, (l ^ 2 + r ^ 2 + 2 * l * r) =
        l ^ 2 + r ^ 2 + 2 * l * r := by
    simp [n]
    field_simp [hn]
  have hl :
      n⁻¹ * ∑ u : γ, (2 * l) * c u = 2 * crossingMean * l := by
    calc
      n⁻¹ * ∑ u : γ, (2 * l) * c u =
          (2 * l) * (n⁻¹ * ∑ u : γ, c u) := by
        rw [← Finset.mul_sum]
        ring
      _ = (2 * l) * crossingMean := by rw [hmean]
      _ = 2 * crossingMean * l := by ring
  have hr :
      n⁻¹ * ∑ u : γ, (2 * r) * c u = 2 * crossingMean * r := by
    calc
      n⁻¹ * ∑ u : γ, (2 * r) * c u =
          (2 * r) * (n⁻¹ * ∑ u : γ, c u) := by
        rw [← Finset.mul_sum]
        ring
      _ = (2 * r) * crossingMean := by rw [hmean]
      _ = 2 * crossingMean * r := by ring
  calc
    n⁻¹ *
        ((∑ u : γ, (c u) ^ 2) +
          (∑ u : γ, (2 * l) * c u) +
          (∑ u : γ, (2 * r) * c u) +
          (∑ _u : γ, (l ^ 2 + r ^ 2 + 2 * l * r))) =
      n⁻¹ * ∑ u : γ, (c u) ^ 2 +
        (n⁻¹ * ∑ u : γ, (2 * l) * c u) +
        (n⁻¹ * ∑ u : γ, (2 * r) * c u) +
        (n⁻¹ * ∑ _u : γ, (l ^ 2 + r ^ 2 + 2 * l * r)) := by ring
    _ = n⁻¹ * ∑ u : γ, (c u) ^ 2 +
        2 * crossingMean * l + 2 * crossingMean * r +
        (l ^ 2 + r ^ 2 + 2 * l * r) := by
      rw [hl, hr, hconst']
    _ = n⁻¹ * ∑ u : γ, (c u) ^ 2 + 2 * l * r +
        l ^ 2 + r ^ 2 + 2 * crossingMean * l + 2 * crossingMean * r := by
      ring

/-- Therefore every remaining term outside the interaction kernel is
boundary-additive and disappears under uniform double centering. -/
theorem finiteUniformAverageComplement_comp_finiteUniformSlabSecondMoment_eq_interaction
    {α : Type} {γ : Type*}
    [Fintype α] [Nonempty α] [Fintype γ] [Nonempty γ]
    (left right : α → ℝ)
    (crossing : γ → α → α → ℝ)
    (crossingMean : ℝ)
    (hMean : ∀ x y : α,
      (Fintype.card γ : ℝ)⁻¹ * ∑ u : γ, crossing u x y = crossingMean) :
    finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (finiteUniformSlabSecondMoment
            (α := α) (γ := γ) left right crossing)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) =
      finiteUniformAverageComplementLinearMap.comp
        ((finiteKernelOperator
          (finiteUniformSlabSecondMomentInteraction
            (α := α) (γ := γ) left right crossing)).toLinearMap.comp
          finiteUniformAverageComplementLinearMap) := by
  apply
    finiteUniformAverageComplement_comp_finiteKernelOperator_congr_of_sub_right_independent
      (α := α)
      (K := finiteUniformSlabSecondMoment
        (α := α) (γ := γ) left right crossing)
      (L := finiteUniformSlabSecondMomentInteraction
        (α := α) (γ := γ) left right crossing)
  intro x x' y y'
  rw [finiteUniformSlabSecondMoment_eq_interaction_add_additive
      left right crossing crossingMean hMean x y,
    finiteUniformSlabSecondMoment_eq_interaction_add_additive
      left right crossing crossingMean hMean x y',
    finiteUniformSlabSecondMoment_eq_interaction_add_additive
      left right crossing crossingMean hMean x' y,
    finiteUniformSlabSecondMoment_eq_interaction_add_additive
      left right crossing crossingMean hMean x' y']
  ring

end

end MathlibAnalytic
end MGAP4D
