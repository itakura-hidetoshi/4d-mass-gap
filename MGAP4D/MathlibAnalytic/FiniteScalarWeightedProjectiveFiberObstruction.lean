import MGAP4D.MathlibAnalytic.FiniteGroupScalarWeightedOrbitFiberCriterion
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Pairwise projective obstruction between two finite coefficient profiles.
It vanishes exactly when the two displayed coefficient pairs have the same
projective ratio, without mentioning any external normalization scalar. -/
def finiteScalarWeightedProjectiveFiberObstruction
    {α : Type}
    (w v : α → ℝ)
    (x y : α) : ℝ :=
  w x * v y - w y * v x

/-- If two coefficient profiles agree after multiplication by one pair of
fixed scalars and the fine scalar is nonzero, then every pairwise projective
obstruction vanishes. -/
theorem finiteScalarWeightedProjectiveFiberObstruction_eq_zero_of_scaled_eq
    {α : Type}
    (af ac : ℝ)
    (w v : α → ℝ)
    (haf : af ≠ 0)
    (h : ∀ x, af * w x = ac * v x)
    (x y : α) :
    finiteScalarWeightedProjectiveFiberObstruction w v x y = 0 := by
  have hx := h x
  have hy := h y
  have hz :
      af * (w x * v y - w y * v x) = 0 := by
    calc
      af * (w x * v y - w y * v x) =
          (af * w x) * v y - (af * w y) * v x := by ring
      _ = (ac * v x) * v y - (ac * v y) * v x := by rw [hx, hy]
      _ = 0 := by ring
  unfold finiteScalarWeightedProjectiveFiberObstruction
  exact (mul_eq_zero.mp hz).resolve_left haf

/-- With one nonzero coarse anchor coefficient and a nonzero fine scalar,
scaled equality of two complete coefficient profiles is equivalent to one
anchor equality plus vanishing of every projective obstruction against that
anchor. -/
theorem finiteScalarWeighted_scaled_eq_all_iff_anchor_and_projective
    {α : Type}
    (af ac : ℝ)
    (w v : α → ℝ)
    (x₀ : α)
    (haf : af ≠ 0)
    (hv₀ : v x₀ ≠ 0) :
    (∀ x, af * w x = ac * v x) ↔
      af * w x₀ = ac * v x₀ ∧
        ∀ x, finiteScalarWeightedProjectiveFiberObstruction w v x x₀ = 0 := by
  constructor
  · intro h
    refine ⟨h x₀, ?_⟩
    intro x
    exact finiteScalarWeightedProjectiveFiberObstruction_eq_zero_of_scaled_eq
      af ac w v haf h x x₀
  · rintro ⟨hAnchor, hProjective⟩ x
    have hRatio : w x * v x₀ = w x₀ * v x := by
      exact sub_eq_zero.mp (hProjective x)
    have hz :
        (af * w x - ac * v x) * v x₀ = 0 := by
      calc
        (af * w x - ac * v x) * v x₀ =
            af * (w x * v x₀) - ac * (v x * v x₀) := by ring
        _ = af * (w x₀ * v x) - ac * (v x * v x₀) := by rw [hRatio]
        _ = (af * w x₀ - ac * v x₀) * v x := by ring
        _ = 0 := by rw [sub_eq_zero.mpr hAnchor]; simp
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hv₀)

/-- A single nonzero projective obstruction certifies failure of any proposed
scaled equality with a nonzero fine scalar. -/
theorem finiteScalarWeighted_scaled_eq_all_false_of_projective_ne_zero
    {α : Type}
    (af ac : ℝ)
    (w v : α → ℝ)
    (haf : af ≠ 0)
    (x y : α)
    (hxy : finiteScalarWeightedProjectiveFiberObstruction w v x y ≠ 0) :
    ¬ ∀ z, af * w z = ac * v z := by
  intro h
  exact hxy
    (finiteScalarWeightedProjectiveFiberObstruction_eq_zero_of_scaled_eq
      af ac w v haf h x y)

end

end MathlibAnalytic
end MGAP4D