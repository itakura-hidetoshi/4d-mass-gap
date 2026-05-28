import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CompletedDiagonalConditionalClosedGraph

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped Topology ENNReal lp

noncomputable section

/-- Coordinate-evaluation continuity surface for the completed `l2` carrier.

This isolates the remaining Mathlib API point: continuity of each coordinate
evaluation map on `lp (fun _ : ℕ => ℝ) 2`. -/
def concreteL2R2CoordinateEvaluationContinuity : Prop :=
  ∀ n : ℕ, Continuous fun x : lp (fun _ : ℕ => ℝ) 2 => x n

/-- Coordinate-evaluation continuity implies the norm/topological-convergence to
coordinatewise-convergence bridge needed by the conditional closed-graph theorem. -/
theorem concrete_l2_r2_norm_convergence_to_coordinatewise_bridge_of_coordinate_continuity
    (hcoord : concreteL2R2CoordinateEvaluationContinuity) :
    concreteL2R2NormConvergenceToCoordinatewiseBridge := by
  intro xs x hxs n
  exact (hcoord n).tendsto x |>.comp hxs

/-- Conditional reduction of the completed diagonal closed graph theorem to
coordinate-evaluation continuity. -/
def concreteL2R2ClosedGraphFromCoordinateContinuity : Prop :=
  concreteL2R2CoordinateEvaluationContinuity →
    ∀ (xs ys : ℕ → lp (fun _ : ℕ => ℝ) 2)
      (x y : lp (fun _ : ℕ => ℝ) 2),
      Filter.Tendsto xs Filter.atTop (𝓝 x) →
      Filter.Tendsto ys Filter.atTop (𝓝 y) →
      (∀ m : ℕ, (xs m, ys m) ∈ concreteL2R2CompletedDiagonalGraphCarrier) →
      (x, y) ∈ concreteL2R2CompletedDiagonalGraphCarrier

/-- From coordinate continuity, the completed diagonal graph is closed under
sequential topological limits in the completed `l2` carrier. -/
theorem concrete_l2_r2_completed_diagonal_closed_graph_from_coordinate_continuity :
    concreteL2R2ClosedGraphFromCoordinateContinuity := by
  intro hcoord xs ys x y hxs hys hgraph
  exact concrete_l2_r2_completed_diagonal_conditional_closed_graph_theorem
    (concrete_l2_r2_norm_convergence_to_coordinatewise_bridge_of_coordinate_continuity hcoord)
    xs ys x y hxs hys hgraph

/-- Public theorem-entry predicate for reducing the closed-graph problem to
coordinate-evaluation continuity. -/
def concreteAnalyticSpineL2R2NormCoordinateBridgeFromContinuityReady : Prop :=
  concreteAnalyticSpineL2R2CompletedDiagonalConditionalClosedGraphReady ∧
  (concreteL2R2CoordinateEvaluationContinuity →
    concreteL2R2NormConvergenceToCoordinatewiseBridge) ∧
  concreteL2R2ClosedGraphFromCoordinateContinuity

/-- The coordinate-continuity bridge reduction layer is ready. -/
theorem concrete_analytic_spine_l2_r2_norm_coordinate_bridge_from_continuity_ready :
    concreteAnalyticSpineL2R2NormCoordinateBridgeFromContinuityReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_completed_diagonal_conditional_closed_graph_ready,
    concrete_l2_r2_norm_convergence_to_coordinatewise_bridge_of_coordinate_continuity,
    concrete_l2_r2_completed_diagonal_closed_graph_from_coordinate_continuity⟩

end

end MathlibAnalytic
end MGAP4D
