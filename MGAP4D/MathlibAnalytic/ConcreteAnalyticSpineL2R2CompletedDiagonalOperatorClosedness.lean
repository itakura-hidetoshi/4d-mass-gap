import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CompletedDiagonalIsClosedGraph

namespace MGAP4D
namespace MathlibAnalytic

open scoped Topology ENNReal lp

noncomputable section

/-- The graph carrier of the graph-defined completed diagonal operator is exactly
the completed diagonal graph carrier. -/
theorem concrete_l2_r2_completed_diagonal_operator_graphCarrier_eq :
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier =
      concreteL2R2CompletedDiagonalGraphCarrier := by
  rfl

/-- The graph-defined completed diagonal operator has a topologically closed
graph carrier. -/
theorem concrete_l2_r2_completed_diagonal_operator_graph_isClosed :
    IsClosed concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier := by
  rw [concrete_l2_r2_completed_diagonal_operator_graphCarrier_eq]
  exact concrete_l2_r2_completed_diagonal_graph_isClosed

/-- Closedness statement for the graph-defined completed diagonal partial
operator. -/
def concreteL2R2CompletedDiagonalGraphDefinedOperatorClosed : Prop :=
  IsClosed concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier

/-- The graph-defined completed diagonal operator is closed in the graph-carrier
sense. -/
theorem concrete_l2_r2_completed_diagonal_graph_defined_operator_closed :
    concreteL2R2CompletedDiagonalGraphDefinedOperatorClosed := by
  exact concrete_l2_r2_completed_diagonal_operator_graph_isClosed

/-- Public theorem-entry predicate for the completed diagonal operator closedness
layer. -/
def concreteAnalyticSpineL2R2CompletedDiagonalOperatorClosednessReady : Prop :=
  concreteAnalyticSpineL2R2CompletedDiagonalIsClosedGraphReady ∧
  concreteL2R2CompletedDiagonalGraphDefinedOperatorClosed ∧
  concreteL2R2CompletedDiagonalGraphDefinedOperatorGrowthCertificate

/-- The completed diagonal graph-defined operator closedness layer is ready. -/
theorem concrete_analytic_spine_l2_r2_completed_diagonal_operator_closedness_ready :
    concreteAnalyticSpineL2R2CompletedDiagonalOperatorClosednessReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_completed_diagonal_isClosed_graph_ready,
    concrete_l2_r2_completed_diagonal_graph_defined_operator_closed,
    concrete_l2_r2_completed_diagonal_graph_defined_operator_growth_certificate⟩

end

end MathlibAnalytic
end MGAP4D
