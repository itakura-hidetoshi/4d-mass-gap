import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2SelfAdjointnessConcretePreconditions

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Algebraic finite-coordinate symmetry of the real diagonal weight.  This is the
finite-sum core behind the later Hilbert-inner-product symmetry statement. -/
theorem concrete_l2_r2_diagonal_weight_finite_coordinate_symmetry
    (s : Finset ℕ) (x z : ℕ → ℝ) :
    Finset.sum s (fun n => (concreteL2DiagonalWeight n * x n) * z n) =
      Finset.sum s (fun n => x n * (concreteL2DiagonalWeight n * z n)) := by
  refine Finset.sum_congr rfl ?_
  intro n _hn
  ring

/-- If two graph pairs lie in the completed diagonal graph carrier, then their
finite coordinate pairings are symmetric. -/
theorem concrete_l2_r2_completed_diagonal_graph_finite_coordinate_symmetry
    (s : Finset ℕ)
    {x Tx z Tz : lp (fun _ : ℕ => ℝ) 2}
    (hxgraph : (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphCarrier)
    (hzgraph : (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphCarrier) :
    Finset.sum s (fun n => (Tx n) * (z n)) =
      Finset.sum s (fun n => (x n) * (Tz n)) := by
  refine Finset.sum_congr rfl ?_
  intro n _hn
  have hx : Tx n = concreteL2DiagonalWeight n * x n := hxgraph n
  have hz : Tz n = concreteL2DiagonalWeight n * z n := hzgraph n
  calc
    (Tx n) * (z n)
        = (concreteL2DiagonalWeight n * x n) * z n := by rw [hx]
    _ = x n * (concreteL2DiagonalWeight n * z n) := by ring
    _ = x n * Tz n := by rw [hz]

/-- The same finite-coordinate symmetry, expressed through the graph-defined
completed diagonal operator's graph carrier. -/
theorem concrete_l2_r2_completed_diagonal_operator_finite_coordinate_symmetry
    (s : Finset ℕ)
    {x Tx z Tz : lp (fun _ : ℕ => ℝ) 2}
    (hxgraph : (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier)
    (hzgraph : (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier) :
    Finset.sum s (fun n => (Tx n) * (z n)) =
      Finset.sum s (fun n => (x n) * (Tz n)) := by
  apply concrete_l2_r2_completed_diagonal_graph_finite_coordinate_symmetry s
  · simpa [concreteL2R2CompletedDiagonalGraphDefinedOperator] using hxgraph
  · simpa [concreteL2R2CompletedDiagonalGraphDefinedOperator] using hzgraph

/-- Public theorem-entry predicate for the finite-coordinate symmetry layer. -/
def concreteAnalyticSpineL2R2DiagonalFiniteCoordinateSymmetryReady : Prop :=
  concreteAnalyticSpineL2R2SelfAdjointnessConcretePreconditionsReady ∧
  (∀ s : Finset ℕ, ∀ x z : ℕ → ℝ,
    Finset.sum s (fun n => (concreteL2DiagonalWeight n * x n) * z n) =
      Finset.sum s (fun n => x n * (concreteL2DiagonalWeight n * z n))) ∧
  (∀ s : Finset ℕ, ∀ x Tx z Tz : lp (fun _ : ℕ => ℝ) 2,
    (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
    (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
    Finset.sum s (fun n => (Tx n) * (z n)) =
      Finset.sum s (fun n => (x n) * (Tz n))) ∧
  True

/-- The finite-coordinate symmetry layer is ready. -/
theorem concrete_analytic_spine_l2_r2_diagonal_finite_coordinate_symmetry_ready :
    concreteAnalyticSpineL2R2DiagonalFiniteCoordinateSymmetryReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_self_adjointness_concrete_preconditions_ready,
    concrete_l2_r2_diagonal_weight_finite_coordinate_symmetry,
    fun s x Tx z Tz hx hz =>
      concrete_l2_r2_completed_diagonal_operator_finite_coordinate_symmetry s hx hz,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
