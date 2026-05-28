import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2NormCoordinateBridgeFromContinuity

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped Topology ENNReal lp

noncomputable section

/-- Coordinate evaluation on the completed `l2` carrier is continuous.

The proof uses the standard `lp.norm_apply_le_norm` estimate: changing an `l2`
vector by a small amount in the ambient `lp` norm changes each coordinate by at
most that amount. -/
theorem concrete_l2_r2_coordinate_evaluation_continuous
    (n : ℕ) :
    Continuous fun x : lp (fun _ : ℕ => ℝ) 2 => x n := by
  rw [Metric.continuous_iff]
  intro x ε hε
  refine ⟨ε, hε, ?_⟩
  intro y hy
  have hsub : (y - x) n = y n - x n := rfl
  calc
    dist ((fun z : lp (fun _ : ℕ => ℝ) 2 => z n) y)
        ((fun z : lp (fun _ : ℕ => ℝ) 2 => z n) x)
        = ‖y n - x n‖ := by
          simp [dist_eq_norm]
    _ = ‖(y - x) n‖ := by
          rw [hsub]
    _ ≤ ‖y - x‖ := by
          exact lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (y - x) n
    _ = dist y x := by
          simp [dist_eq_norm]
    _ < ε := hy

/-- Coordinate-evaluation continuity for all coordinates of the completed `l2`
carrier. -/
theorem concrete_l2_r2_coordinate_evaluation_continuity :
    concreteL2R2CoordinateEvaluationContinuity := by
  intro n
  exact concrete_l2_r2_coordinate_evaluation_continuous n

/-- The unconditional norm/topological-convergence to coordinatewise-convergence
bridge for the completed `l2` carrier. -/
theorem concrete_l2_r2_norm_convergence_to_coordinatewise_bridge :
    concreteL2R2NormConvergenceToCoordinatewiseBridge := by
  exact concrete_l2_r2_norm_convergence_to_coordinatewise_bridge_of_coordinate_continuity
    concrete_l2_r2_coordinate_evaluation_continuity

/-- The completed diagonal graph is closed under sequential topological limits in
`lp`, now using the concrete coordinate-evaluation continuity theorem. -/
theorem concrete_l2_r2_completed_diagonal_closed_graph_sequential :
    ∀ (xs ys : ℕ → lp (fun _ : ℕ => ℝ) 2)
      (x y : lp (fun _ : ℕ => ℝ) 2),
      Filter.Tendsto xs Filter.atTop (𝓝 x) →
      Filter.Tendsto ys Filter.atTop (𝓝 y) →
      (∀ m : ℕ, (xs m, ys m) ∈ concreteL2R2CompletedDiagonalGraphCarrier) →
      (x, y) ∈ concreteL2R2CompletedDiagonalGraphCarrier := by
  exact concrete_l2_r2_completed_diagonal_conditional_closed_graph_theorem
    concrete_l2_r2_norm_convergence_to_coordinatewise_bridge

/-- Public theorem-entry predicate for coordinate-evaluation continuity and the
unconditional norm-to-coordinate bridge. -/
def concreteAnalyticSpineL2R2CoordinateEvaluationContinuityReady : Prop :=
  concreteAnalyticSpineL2R2NormCoordinateBridgeFromContinuityReady ∧
  concreteL2R2CoordinateEvaluationContinuity ∧
  concreteL2R2NormConvergenceToCoordinatewiseBridge ∧
  (∀ (xs ys : ℕ → lp (fun _ : ℕ => ℝ) 2)
      (x y : lp (fun _ : ℕ => ℝ) 2),
      Filter.Tendsto xs Filter.atTop (𝓝 x) →
      Filter.Tendsto ys Filter.atTop (𝓝 y) →
      (∀ m : ℕ, (xs m, ys m) ∈ concreteL2R2CompletedDiagonalGraphCarrier) →
      (x, y) ∈ concreteL2R2CompletedDiagonalGraphCarrier)

/-- The coordinate-evaluation continuity layer is ready. -/
theorem concrete_analytic_spine_l2_r2_coordinate_evaluation_continuity_ready :
    concreteAnalyticSpineL2R2CoordinateEvaluationContinuityReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_norm_coordinate_bridge_from_continuity_ready,
    concrete_l2_r2_coordinate_evaluation_continuity,
    concrete_l2_r2_norm_convergence_to_coordinatewise_bridge,
    concrete_l2_r2_completed_diagonal_closed_graph_sequential⟩

end

end MathlibAnalytic
end MGAP4D
