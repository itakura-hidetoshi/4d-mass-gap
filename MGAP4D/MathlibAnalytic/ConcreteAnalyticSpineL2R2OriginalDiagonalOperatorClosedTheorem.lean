import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DiagonalGraphEqualsClosureBridge

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Closedness of the original R2 diagonal graph. -/
def concreteL2R2OriginalDiagonalGraphClosedTheorem : Prop :=
  @IsClosed ConcreteL2GraphPairSpace concreteL2GraphNormTopology
    ConcreteL2DiagonalGraphL2Carrier

/-- If the original diagonal graph equals the closure-generated graph, then the
original diagonal graph is closed.

The proof transports the already-proved closure-generated closed-operator theorem
across the graph equality. -/
theorem concrete_l2_r2_original_diagonal_graph_closed_of_equals_closure
    (hEq : concreteL2R2DiagonalGraphEqualsClosureGeneratedGraph) :
    concreteL2R2OriginalDiagonalGraphClosedTheorem := by
  unfold concreteL2R2OriginalDiagonalGraphClosedTheorem
  unfold concreteL2R2DiagonalGraphEqualsClosureGeneratedGraph at hEq
  rw [hEq]
  exact concrete_l2_r2_closed_operator_theorem

/-- Conditional original diagonal operator closed theorem.

This keeps the missing reverse inclusion visible: the original diagonal operator
closed theorem follows once diagonal-graph-equals-closure is supplied. -/
def concreteL2R2OriginalDiagonalOperatorClosedTheoremConditional : Prop :=
  concreteL2R2DiagonalGraphEqualsClosureGeneratedGraph →
    concreteL2R2OriginalDiagonalGraphClosedTheorem

/-- The conditional original diagonal operator closed theorem is proved. -/
theorem concrete_l2_r2_original_diagonal_operator_closed_theorem_conditional :
    concreteL2R2OriginalDiagonalOperatorClosedTheoremConditional := by
  intro hEq
  exact concrete_l2_r2_original_diagonal_graph_closed_of_equals_closure hEq

/-- Readiness predicate for the conditional original diagonal operator closed theorem. -/
def concreteAnalyticSpineL2R2OriginalDiagonalOperatorClosedTheoremConditionalReady : Prop :=
  concreteL2R2OriginalDiagonalOperatorClosedTheoremConditional ∧
  concreteL2R2DiagonalGraphEqualsClosureBridgeReady ∧
  True

/-- The conditional original diagonal operator closed theorem surface is ready. -/
theorem concrete_analytic_spine_l2_r2_original_diagonal_operator_closed_theorem_conditional_ready :
    concreteAnalyticSpineL2R2OriginalDiagonalOperatorClosedTheoremConditionalReady := by
  exact ⟨
    concrete_l2_r2_original_diagonal_operator_closed_theorem_conditional,
    concrete_analytic_spine_l2_r2_diagonal_graph_equals_closure_bridge_ready,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
