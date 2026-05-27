import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2OriginalDiagonalOperatorClosedTheorem

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The finite-support core graph is contained in the original diagonal graph. -/
def concreteL2R2FiniteSupportCoreGraphSubsetDiagonalGraph : Prop :=
  ConcreteL2FiniteSupportCoreGraphCarrier ⊆ ConcreteL2DiagonalGraphL2Carrier

/-- The finite-support core graph is contained in the original diagonal graph.

This is inherited from the R2 graph-pair transport scaffold theorem. -/
theorem concrete_l2_r2_finite_support_core_graph_subset_diagonal_graph :
    concreteL2R2FiniteSupportCoreGraphSubsetDiagonalGraph := by
  exact concrete_l2_finite_support_core_graph_subset_diagonal_graph_l2

/-- Criterion for the reverse inclusion needed by diagonal-graph-equals-closure.

If the original diagonal graph is closed and contains the finite-support core
graph, then the graph-norm closure of the finite-support core graph is contained
in the original diagonal graph. -/
theorem concrete_l2_r2_closure_generated_graph_subset_diagonal_graph_of_closed_and_core_subset
    (hClosed : concreteL2R2OriginalDiagonalGraphClosedTheorem)
    (hCore : concreteL2R2FiniteSupportCoreGraphSubsetDiagonalGraph) :
    concreteL2R2ClosureGeneratedGraphSubsetDiagonalGraphObligation := by
  unfold concreteL2R2ClosureGeneratedGraphSubsetDiagonalGraphObligation
  unfold ConcreteL2R2ClosureGeneratedOperatorGraph
  unfold concreteL2R2OriginalDiagonalGraphClosedTheorem at hClosed
  exact @closure_minimal ConcreteL2GraphPairSpace concreteL2GraphNormTopology
    ConcreteL2FiniteSupportCoreGraphCarrier ConcreteL2DiagonalGraphL2Carrier hCore hClosed

/-- Conditional reverse inclusion criterion. -/
def concreteL2R2ClosureSubsetDiagonalCriterion : Prop :=
  concreteL2R2OriginalDiagonalGraphClosedTheorem →
  concreteL2R2FiniteSupportCoreGraphSubsetDiagonalGraph →
  concreteL2R2ClosureGeneratedGraphSubsetDiagonalGraphObligation

/-- The closure-subset-diagonal criterion is ready. -/
theorem concrete_l2_r2_closure_subset_diagonal_criterion :
    concreteL2R2ClosureSubsetDiagonalCriterion := by
  intro hClosed hCore
  exact concrete_l2_r2_closure_generated_graph_subset_diagonal_graph_of_closed_and_core_subset
    hClosed hCore

/-- Conditional reverse inclusion using the proven finite-support core inclusion. -/
def concreteL2R2ClosureSubsetDiagonalFromOriginalClosed : Prop :=
  concreteL2R2OriginalDiagonalGraphClosedTheorem →
    concreteL2R2ClosureGeneratedGraphSubsetDiagonalGraphObligation

/-- If the original diagonal graph is closed, then the closure-generated graph is
contained in it. -/
theorem concrete_l2_r2_closure_subset_diagonal_from_original_closed :
    concreteL2R2ClosureSubsetDiagonalFromOriginalClosed := by
  intro hClosed
  exact concrete_l2_r2_closure_generated_graph_subset_diagonal_graph_of_closed_and_core_subset
    hClosed concrete_l2_r2_finite_support_core_graph_subset_diagonal_graph

/-- Readiness predicate for the reverse-inclusion criterion. -/
def concreteAnalyticSpineL2R2ClosureSubsetDiagonalCriterionReady : Prop :=
  concreteL2R2FiniteSupportCoreGraphSubsetDiagonalGraph ∧
  concreteL2R2ClosureSubsetDiagonalCriterion ∧
  concreteL2R2ClosureSubsetDiagonalFromOriginalClosed ∧
  concreteAnalyticSpineL2R2OriginalDiagonalOperatorClosedTheoremConditionalReady ∧
  True

/-- The reverse-inclusion criterion surface is ready. -/
theorem concrete_analytic_spine_l2_r2_closure_subset_diagonal_criterion_ready :
    concreteAnalyticSpineL2R2ClosureSubsetDiagonalCriterionReady := by
  exact ⟨
    concrete_l2_r2_finite_support_core_graph_subset_diagonal_graph,
    concrete_l2_r2_closure_subset_diagonal_criterion,
    concrete_l2_r2_closure_subset_diagonal_from_original_closed,
    concrete_analytic_spine_l2_r2_original_diagonal_operator_closed_theorem_conditional_ready,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
