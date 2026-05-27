import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DiagonalGraphSubsetClosure
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DomainActionDenseObligations

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The missing reverse inclusion for the R2 diagonal-graph-equals-closure step.

This is the remaining mathematical obligation: every point in the
closure-generated graph must be represented by the original diagonal graph. -/
def concreteL2R2ClosureGeneratedGraphSubsetDiagonalGraphObligation : Prop :=
  ConcreteL2R2ClosureGeneratedOperatorGraph ⊆ ConcreteL2DiagonalGraphL2Carrier

/-- The full diagonal-graph-equals-closure statement for R2. -/
def concreteL2R2DiagonalGraphEqualsClosureGeneratedGraph : Prop :=
  ConcreteL2DiagonalGraphL2Carrier = ConcreteL2R2ClosureGeneratedOperatorGraph

/-- If the reverse inclusion is supplied, then the diagonal graph equals the
closure-generated graph.

The forward inclusion is the proved graph-norm finite-support density theorem;
the reverse inclusion is left as the explicit closure-uniqueness obligation. -/
theorem concrete_l2_r2_diagonal_graph_equals_closure_generated_graph_of_reverse_subset
    (hReverse : concreteL2R2ClosureGeneratedGraphSubsetDiagonalGraphObligation) :
    concreteL2R2DiagonalGraphEqualsClosureGeneratedGraph := by
  unfold concreteL2R2DiagonalGraphEqualsClosureGeneratedGraph
  exact Set.Subset.antisymm
    concrete_l2_r2_diagonal_graph_subset_closure_generated_graph
    hReverse

/-- Conditional bridge packet for diagonal-graph-equals-closure. -/
def concreteL2R2DiagonalGraphEqualsClosureBridgeReady : Prop :=
  concreteAnalyticSpineL2R2DiagonalGraphSubsetClosureReady ∧
  concreteL2R2DomainActionDenseObligationsClosedPacket ∧
  True

/-- The conditional diagonal-graph-equals-closure bridge is ready. -/
theorem concrete_analytic_spine_l2_r2_diagonal_graph_equals_closure_bridge_ready :
    concreteL2R2DiagonalGraphEqualsClosureBridgeReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_diagonal_graph_subset_closure_ready,
    concrete_l2_r2_domain_action_dense_obligations_closed_packet_ready,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
