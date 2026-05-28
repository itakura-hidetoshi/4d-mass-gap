import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CompletedDiagonalClosedGraphRouteSurface

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped Topology ENNReal lp

noncomputable section

/-- The remaining analytic bridge needed to upgrade coordinatewise closedness to
a full completed `l2` closed-graph theorem: norm/topological convergence in
`lp` implies coordinatewise convergence. -/
def concreteL2R2NormConvergenceToCoordinatewiseBridge : Prop :=
  ∀ (xs : ℕ → lp (fun _ : ℕ => ℝ) 2) (x : lp (fun _ : ℕ => ℝ) 2),
    Filter.Tendsto xs Filter.atTop (𝓝 x) →
    ∀ n : ℕ, Filter.Tendsto (fun m : ℕ => xs m n) Filter.atTop (𝓝 (x n))

/-- Closed-graph theorem for the completed diagonal graph, conditional only on
the standard `lp` bridge from norm/topological convergence to coordinatewise
convergence. -/
def concreteL2R2CompletedDiagonalConditionalClosedGraphTheorem : Prop :=
  concreteL2R2NormConvergenceToCoordinatewiseBridge →
    ∀ (xs ys : ℕ → lp (fun _ : ℕ => ℝ) 2)
      (x y : lp (fun _ : ℕ => ℝ) 2),
      Filter.Tendsto xs Filter.atTop (𝓝 x) →
      Filter.Tendsto ys Filter.atTop (𝓝 y) →
      (∀ m : ℕ, (xs m, ys m) ∈ concreteL2R2CompletedDiagonalGraphCarrier) →
      (x, y) ∈ concreteL2R2CompletedDiagonalGraphCarrier

/-- Conditional completed diagonal closed graph theorem.

Once the norm/topological-to-coordinatewise convergence bridge is supplied, the
closed graph statement follows immediately from the coordinatewise closedness
layer. -/
theorem concrete_l2_r2_completed_diagonal_conditional_closed_graph_theorem :
    concreteL2R2CompletedDiagonalConditionalClosedGraphTheorem := by
  intro hbridge xs ys x y hxs hys hgraph
  exact concrete_l2_r2_completed_diagonal_graph_coordinatewise_closed
    xs ys x y (hbridge xs x hxs) (hbridge ys y hys) hgraph

/-- Public theorem-entry predicate for the conditional closed-graph theorem. -/
def concreteAnalyticSpineL2R2CompletedDiagonalConditionalClosedGraphReady : Prop :=
  concreteAnalyticSpineL2R2CompletedDiagonalClosedGraphRouteSurfaceReady ∧
  concreteL2R2CompletedDiagonalConditionalClosedGraphTheorem ∧
  True

/-- The conditional completed diagonal closed-graph layer is ready. -/
theorem concrete_analytic_spine_l2_r2_completed_diagonal_conditional_closed_graph_ready :
    concreteAnalyticSpineL2R2CompletedDiagonalConditionalClosedGraphReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_completed_diagonal_closed_graph_route_surface_ready,
    concrete_l2_r2_completed_diagonal_conditional_closed_graph_theorem,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
