import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CompletedDiagonalOperatorDefinition

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Coordinatewise equality implies equality for completed `l2` vectors.

This isolates the `lp` extensionality API used by the completed diagonal graph
single-valuedness proof. -/
theorem concrete_l2_r2_completed_l2_ext
    {u v : lp (fun _ : ℕ => ℝ) 2}
    (h : ∀ n : ℕ, u n = v n) :
    u = v := by
  ext n
  exact h n

/-- The full completed diagonal graph carrier is single-valued: two graph outputs
for the same input must be equal coordinatewise. -/
theorem concrete_l2_r2_completed_diagonal_graph_single_valued
    {x y₁ y₂ : lp (fun _ : ℕ => ℝ) 2}
    (hy₁ : (x, y₁) ∈ concreteL2R2CompletedDiagonalGraphCarrier)
    (hy₂ : (x, y₂) ∈ concreteL2R2CompletedDiagonalGraphCarrier) :
    y₁ = y₂ := by
  apply concrete_l2_r2_completed_l2_ext
  intro n
  calc
    y₁ n = concreteL2DiagonalWeight n * x n := hy₁ n
    _ = y₂ n := (hy₂ n).symm

/-- Single-valuedness predicate for the graph-defined completed diagonal
operator. -/
def concreteL2R2CompletedDiagonalSingleValuednessTheorem : Prop :=
  ∀ x y₁ y₂ : lp (fun _ : ℕ => ℝ) 2,
    (x, y₁) ∈ concreteL2R2CompletedDiagonalGraphCarrier →
    (x, y₂) ∈ concreteL2R2CompletedDiagonalGraphCarrier →
    y₁ = y₂

/-- The graph-defined completed diagonal operator is single-valued. -/
theorem concrete_l2_r2_completed_diagonal_single_valuedness_theorem :
    concreteL2R2CompletedDiagonalSingleValuednessTheorem := by
  intro x y₁ y₂ hy₁ hy₂
  exact concrete_l2_r2_completed_diagonal_graph_single_valued hy₁ hy₂

/-- Public theorem-entry predicate for completed diagonal single-valuedness. -/
def concreteAnalyticSpineL2R2CompletedDiagonalSingleValuednessReady : Prop :=
  concreteAnalyticSpineL2R2CompletedDiagonalOperatorDefinitionReady ∧
  concreteL2R2CompletedDiagonalSingleValuednessTheorem

/-- The completed diagonal single-valuedness layer is ready. -/
theorem concrete_analytic_spine_l2_r2_completed_diagonal_single_valuedness_ready :
    concreteAnalyticSpineL2R2CompletedDiagonalSingleValuednessReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_completed_diagonal_operator_definition_ready,
    concrete_l2_r2_completed_diagonal_single_valuedness_theorem⟩

end

end MathlibAnalytic
end MGAP4D
