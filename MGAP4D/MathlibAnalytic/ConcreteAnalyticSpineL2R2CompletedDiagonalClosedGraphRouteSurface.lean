import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CompletedDiagonalCoordinatewiseClosedness

namespace MGAP4D
namespace MathlibAnalytic

open Filter Topology
open scoped ENNReal lp

noncomputable section

/-- Consolidated route surface toward the completed diagonal closed-graph theorem.

This surface deliberately stops at coordinatewise closedness.  The remaining
bridge from completed `l2` norm convergence to coordinatewise convergence is
kept explicit, so the full closed-graph theorem is not prematurely claimed. -/
structure ConcreteL2R2CompletedDiagonalClosedGraphRouteSurface where
  unboundedOperatorSurfaceReady : concreteL2R2CompletedDiagonalUnboundedOperatorSurfaceReady
  coordinatewiseClosednessReady :
    concreteAnalyticSpineL2R2CompletedDiagonalCoordinatewiseClosednessReady
  coordinatewiseClosedness :
    ∀ (xs ys : ℕ → lp (fun _ : ℕ => ℝ) 2)
      (x y : lp (fun _ : ℕ => ℝ) 2),
      (∀ n : ℕ, Filter.Tendsto (fun m : ℕ => xs m n) Filter.atTop (𝓝 (x n))) →
      (∀ n : ℕ, Filter.Tendsto (fun m : ℕ => ys m n) Filter.atTop (𝓝 (y n))) →
      (∀ m : ℕ, (xs m, ys m) ∈ concreteL2R2CompletedDiagonalGraphCarrier) →
      (x, y) ∈ concreteL2R2CompletedDiagonalGraphCarrier
  boundaryNotNormConvergenceToCoordinatewiseBridge : Prop
  boundaryNotCompletedClosedGraphTheorem : Prop

/-- The completed diagonal closed-graph route surface. -/
def concreteL2R2CompletedDiagonalClosedGraphRouteSurface :
    ConcreteL2R2CompletedDiagonalClosedGraphRouteSurface :=
  { unboundedOperatorSurfaceReady :=
      concrete_analytic_spine_l2_r2_completed_diagonal_unbounded_operator_surface_ready
    coordinatewiseClosednessReady :=
      concrete_analytic_spine_l2_r2_completed_diagonal_coordinatewise_closedness_ready
    coordinatewiseClosedness :=
      concrete_l2_r2_completed_diagonal_graph_coordinatewise_closed
    boundaryNotNormConvergenceToCoordinatewiseBridge := True
    boundaryNotCompletedClosedGraphTheorem := True }

/-- Public theorem-entry predicate for the completed diagonal closed-graph route
surface. -/
def concreteAnalyticSpineL2R2CompletedDiagonalClosedGraphRouteSurfaceReady : Prop :=
  concreteL2R2CompletedDiagonalUnboundedOperatorSurfaceReady ∧
  concreteAnalyticSpineL2R2CompletedDiagonalCoordinatewiseClosednessReady ∧
  (∀ (xs ys : ℕ → lp (fun _ : ℕ => ℝ) 2)
      (x y : lp (fun _ : ℕ => ℝ) 2),
      (∀ n : ℕ, Filter.Tendsto (fun m : ℕ => xs m n) Filter.atTop (𝓝 (x n))) →
      (∀ n : ℕ, Filter.Tendsto (fun m : ℕ => ys m n) Filter.atTop (𝓝 (y n))) →
      (∀ m : ℕ, (xs m, ys m) ∈ concreteL2R2CompletedDiagonalGraphCarrier) →
      (x, y) ∈ concreteL2R2CompletedDiagonalGraphCarrier) ∧
  True ∧ True

/-- The completed diagonal closed-graph route surface is ready. -/
theorem concrete_analytic_spine_l2_r2_completed_diagonal_closed_graph_route_surface_ready :
    concreteAnalyticSpineL2R2CompletedDiagonalClosedGraphRouteSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_completed_diagonal_unbounded_operator_surface_ready,
    concrete_analytic_spine_l2_r2_completed_diagonal_coordinatewise_closedness_ready,
    concrete_l2_r2_completed_diagonal_graph_coordinatewise_closed,
    trivial,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
