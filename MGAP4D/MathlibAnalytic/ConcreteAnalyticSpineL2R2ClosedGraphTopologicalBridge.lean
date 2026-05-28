import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CoordinateEvaluationContinuity

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped Topology ENNReal lp

noncomputable section

/-- Sequential closedness statement already proved for the completed diagonal
graph. -/
def concreteL2R2CompletedDiagonalSequentialClosedGraph : Prop :=
  ∀ (xs ys : ℕ → lp (fun _ : ℕ => ℝ) 2)
    (x y : lp (fun _ : ℕ => ℝ) 2),
    Filter.Tendsto xs Filter.atTop (𝓝 x) →
    Filter.Tendsto ys Filter.atTop (𝓝 y) →
    (∀ m : ℕ, (xs m, ys m) ∈ concreteL2R2CompletedDiagonalGraphCarrier) →
    (x, y) ∈ concreteL2R2CompletedDiagonalGraphCarrier

/-- The remaining general-topology bridge: sequential closedness of this graph in
the metric completed `l2 × l2` carrier upgrades to topological closedness of the
set.  This is isolated as a bridge so no full `IsClosed` claim is made until the
Mathlib sequential-closed API is selected. -/
def concreteL2R2SequentialClosedGraphToIsClosedBridge : Prop :=
  concreteL2R2CompletedDiagonalSequentialClosedGraph →
    IsClosed concreteL2R2CompletedDiagonalGraphCarrier

/-- Conditional full topological closed-graph theorem. -/
def concreteL2R2CompletedDiagonalTopologicalClosedGraphConditional : Prop :=
  concreteL2R2SequentialClosedGraphToIsClosedBridge →
    IsClosed concreteL2R2CompletedDiagonalGraphCarrier

/-- The completed diagonal graph is topologically closed, conditional only on the
standard metric-space bridge from sequential closedness to closedness. -/
theorem concrete_l2_r2_completed_diagonal_topological_closed_graph_conditional :
    concreteL2R2CompletedDiagonalTopologicalClosedGraphConditional := by
  intro hbridge
  exact hbridge concrete_l2_r2_completed_diagonal_closed_graph_sequential

/-- Public theorem-entry predicate for the topological closed-graph bridge layer. -/
def concreteAnalyticSpineL2R2ClosedGraphTopologicalBridgeReady : Prop :=
  concreteAnalyticSpineL2R2CoordinateEvaluationContinuityReady ∧
  concreteL2R2CompletedDiagonalSequentialClosedGraph ∧
  concreteL2R2CompletedDiagonalTopologicalClosedGraphConditional ∧
  True

/-- The topological closed-graph bridge layer is ready. -/
theorem concrete_analytic_spine_l2_r2_closed_graph_topological_bridge_ready :
    concreteAnalyticSpineL2R2ClosedGraphTopologicalBridgeReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_coordinate_evaluation_continuity_ready,
    concrete_l2_r2_completed_diagonal_closed_graph_sequential,
    concrete_l2_r2_completed_diagonal_topological_closed_graph_conditional,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
