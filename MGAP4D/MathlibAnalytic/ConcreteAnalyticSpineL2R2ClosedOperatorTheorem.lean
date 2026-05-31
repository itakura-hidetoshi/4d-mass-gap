import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphClosureClosedTheorem
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2ClosedOperatorTheoremObligationPacket
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2ResidualZeroAuditSurface

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The closure-generated R2 operator graph.

This is the graph-norm closure of the finite-support core graph.  It is the
closed graph currently available in the concrete R2 route.  The separate theorem
identifying the original diagonal graph with this closure is intentionally not
assumed here. -/
abbrev ConcreteL2R2ClosureGeneratedOperatorGraph : Set ConcreteL2GraphPairSpace :=
  concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget

/-- Closed-operator theorem for the closure-generated R2 operator graph.

Mathematically, this is the closed-graph statement supplied by Mathlib's
`isClosed_closure`: the graph obtained as the graph-norm closure of the
finite-support core graph is closed.

This is the final closed-graph theorem for the closure-generated operator
surface.  It does not identify the original diagonal graph with this closure and
therefore does not yet promote the original diagonal operator itself. -/
def concreteL2R2ClosedOperatorTheorem : Prop :=
  @IsClosed ConcreteL2GraphPairSpace concreteL2GraphNormTopology
    ConcreteL2R2ClosureGeneratedOperatorGraph

/-- The closure-generated R2 operator graph is closed.

The proof is exactly the Mathlib topological closure theorem specialized to the
R2 graph-norm topology. -/
theorem concrete_l2_r2_closed_operator_theorem :
    concreteL2R2ClosedOperatorTheorem := by
  unfold concreteL2R2ClosedOperatorTheorem
  unfold ConcreteL2R2ClosureGeneratedOperatorGraph
  exact concrete_l2_r2_graph_norm_closure_carrier_closed

/-- Closed-graph theorem with its audit context.

The promoted theorem is paired only with existing proof-bearing audit inputs:
the closed-operator obligation packet and the R2 residual-zero theorem. -/
def concreteL2R2ClosedOperatorTheoremWithAudit : Prop :=
  concreteL2R2ClosedOperatorTheorem ∧
  concreteAnalyticSpineL2R2ClosedOperatorTheoremObligationPacketReady ∧
  concreteL2R2ResidualZeroAtGraphNormCoreLayer

/-- The audited R2 closure-generated closed-graph theorem is ready. -/
theorem concrete_l2_r2_closed_operator_theorem_with_audit :
    concreteL2R2ClosedOperatorTheoremWithAudit := by
  exact ⟨
    concrete_l2_r2_closed_operator_theorem,
    concrete_analytic_spine_l2_r2_closed_operator_theorem_obligation_packet_ready,
    concrete_l2_r2_residual_zero_at_graph_norm_core_layer⟩

/-- Public theorem-entry predicate for the R2 closure-generated closed-graph
surface. -/
def concreteAnalyticSpineL2R2ClosedOperatorTheoremReady : Prop :=
  concreteL2R2ClosedOperatorTheoremWithAudit

/-- The R2 closure-generated closed-graph theorem surface is ready. -/
theorem concrete_analytic_spine_l2_r2_closed_operator_theorem_ready :
    concreteAnalyticSpineL2R2ClosedOperatorTheoremReady := by
  exact concrete_l2_r2_closed_operator_theorem_with_audit

end

end MathlibAnalytic
end MGAP4D
