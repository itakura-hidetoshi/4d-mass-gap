import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CompletedDiagonalUnboundedOperatorSurface
import Mathlib.Topology.Separation.Hausdorff

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped Topology ENNReal lp

noncomputable section

/-- Coordinatewise closedness of the completed diagonal graph relation.

If a sequence of graph pairs `(x_m, y_m)` converges coordinatewise to `(x, y)`,
then the limit pair still satisfies the completed diagonal graph relation.  This
is the clean analytic core behind the later full closed-graph theorem. -/
theorem concrete_l2_r2_completed_diagonal_graph_coordinatewise_closed
    (xs ys : ℕ → lp (fun _ : ℕ => ℝ) 2)
    (x y : lp (fun _ : ℕ => ℝ) 2)
    (hx : ∀ n : ℕ, Filter.Tendsto (fun m : ℕ => xs m n) Filter.atTop (𝓝 (x n)))
    (hy : ∀ n : ℕ, Filter.Tendsto (fun m : ℕ => ys m n) Filter.atTop (𝓝 (y n)))
    (hgraph : ∀ m : ℕ, (xs m, ys m) ∈ concreteL2R2CompletedDiagonalGraphCarrier) :
    (x, y) ∈ concreteL2R2CompletedDiagonalGraphCarrier := by
  intro n
  let c : ℝ := concreteL2DiagonalWeight n
  have hmulCont : Continuous fun z : ℝ => c * z := by
    simpa using (continuous_const.mul continuous_id : Continuous fun z : ℝ => c * z)
  have hmul : Filter.Tendsto (fun m : ℕ => c * xs m n) Filter.atTop (𝓝 (c * x n)) := by
    simpa using (hmulCont.tendsto (x n)).comp (hx n)
  have hfun : (fun m : ℕ => ys m n) = fun m : ℕ => c * xs m n := by
    funext m
    exact hgraph m n
  have hy_as_mul : Filter.Tendsto (fun m : ℕ => c * xs m n) Filter.atTop (𝓝 (y n)) := by
    simpa [hfun] using hy n
  exact tendsto_nhds_unique hy_as_mul hmul

/-- Public theorem-entry predicate for coordinatewise closedness of the completed
diagonal graph. -/
def concreteAnalyticSpineL2R2CompletedDiagonalCoordinatewiseClosednessReady : Prop :=
  concreteL2R2CompletedDiagonalUnboundedOperatorSurfaceReady ∧
  (∀ (xs ys : ℕ → lp (fun _ : ℕ => ℝ) 2)
      (x y : lp (fun _ : ℕ => ℝ) 2),
      (∀ n : ℕ, Filter.Tendsto (fun m : ℕ => xs m n) Filter.atTop (𝓝 (x n))) →
      (∀ n : ℕ, Filter.Tendsto (fun m : ℕ => ys m n) Filter.atTop (𝓝 (y n))) →
      (∀ m : ℕ, (xs m, ys m) ∈ concreteL2R2CompletedDiagonalGraphCarrier) →
      (x, y) ∈ concreteL2R2CompletedDiagonalGraphCarrier)

/-- The coordinatewise closedness layer is ready. -/
theorem concrete_analytic_spine_l2_r2_completed_diagonal_coordinatewise_closedness_ready :
    concreteAnalyticSpineL2R2CompletedDiagonalCoordinatewiseClosednessReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_completed_diagonal_unbounded_operator_surface_ready,
    concrete_l2_r2_completed_diagonal_graph_coordinatewise_closed⟩

end

end MathlibAnalytic
end MGAP4D
