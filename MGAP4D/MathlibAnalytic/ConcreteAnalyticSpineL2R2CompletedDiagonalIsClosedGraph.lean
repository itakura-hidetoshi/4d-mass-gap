import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2ClosedGraphTopologicalBridge

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- Each coordinate graph condition of the completed diagonal graph is closed. -/
theorem concrete_l2_r2_completed_diagonal_coordinate_graph_condition_closed
    (n : ℕ) :
    IsClosed {p : (lp (fun _ : ℕ => ℝ) 2) × (lp (fun _ : ℕ => ℝ) 2) |
      p.2 n = concreteL2DiagonalWeight n * p.1 n} := by
  have hleft : Continuous fun p : (lp (fun _ : ℕ => ℝ) 2) × (lp (fun _ : ℕ => ℝ) 2) =>
      p.2 n := by
    exact (concrete_l2_r2_coordinate_evaluation_continuous n).comp continuous_snd
  have hright : Continuous fun p : (lp (fun _ : ℕ => ℝ) 2) × (lp (fun _ : ℕ => ℝ) 2) =>
      concreteL2DiagonalWeight n * p.1 n := by
    exact continuous_const.mul
      ((concrete_l2_r2_coordinate_evaluation_continuous n).comp continuous_fst)
  exact isClosed_eq hleft hright

/-- The completed diagonal graph carrier is a topologically closed set in the
completed `l2 × l2` carrier. -/
theorem concrete_l2_r2_completed_diagonal_graph_isClosed :
    IsClosed concreteL2R2CompletedDiagonalGraphCarrier := by
  let S : ℕ → Set ((lp (fun _ : ℕ => ℝ) 2) × (lp (fun _ : ℕ => ℝ) 2)) :=
    fun n => {p | p.2 n = concreteL2DiagonalWeight n * p.1 n}
  have hclosed : IsClosed (⋂ n : ℕ, S n) := by
    exact isClosed_iInter fun n : ℕ =>
      concrete_l2_r2_completed_diagonal_coordinate_graph_condition_closed n
  have hset : concreteL2R2CompletedDiagonalGraphCarrier = ⋂ n : ℕ, S n := by
    ext p
    simp [concreteL2R2CompletedDiagonalGraphCarrier, S]
  rw [hset]
  exact hclosed

/-- The sequential-to-closed bridge is now discharged by the direct closed-set
proof.  The premise is retained to match the bridge API, but the proof no longer
needs to use it. -/
theorem concrete_l2_r2_sequential_closed_graph_to_isClosed_bridge :
    concreteL2R2SequentialClosedGraphToIsClosedBridge := by
  intro _hseq
  exact concrete_l2_r2_completed_diagonal_graph_isClosed

/-- Public theorem-entry predicate for the full topological closed graph theorem. -/
def concreteAnalyticSpineL2R2CompletedDiagonalIsClosedGraphReady : Prop :=
  concreteAnalyticSpineL2R2ClosedGraphTopologicalBridgeReady ∧
  IsClosed concreteL2R2CompletedDiagonalGraphCarrier ∧
  concreteL2R2SequentialClosedGraphToIsClosedBridge

/-- The completed diagonal topological closed-graph theorem is ready. -/
theorem concrete_analytic_spine_l2_r2_completed_diagonal_isClosed_graph_ready :
    concreteAnalyticSpineL2R2CompletedDiagonalIsClosedGraphReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_closed_graph_topological_bridge_ready,
    concrete_l2_r2_completed_diagonal_graph_isClosed,
    concrete_l2_r2_sequential_closed_graph_to_isClosed_bridge⟩

end

end MathlibAnalytic
end MGAP4D
