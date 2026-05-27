import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2ClosedOperatorTheorem
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDensityClosedSurface

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The R2 diagonal graph is contained in the closure-generated operator graph.

This is the first half of the future diagonal-graph-equals-closure theorem.  It
is exactly the closed graph-norm finite-support density theorem, re-expressed in
operator-graph language. -/
def concreteL2R2DiagonalGraphSubsetClosureGeneratedGraph : Prop :=
  ConcreteL2DiagonalGraphL2Carrier ⊆ ConcreteL2R2ClosureGeneratedOperatorGraph

/-- The diagonal graph lies in the closure-generated operator graph. -/
theorem concrete_l2_r2_diagonal_graph_subset_closure_generated_graph :
    concreteL2R2DiagonalGraphSubsetClosureGeneratedGraph := by
  unfold concreteL2R2DiagonalGraphSubsetClosureGeneratedGraph
  unfold ConcreteL2R2ClosureGeneratedOperatorGraph
  exact concrete_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_density_closed

/-- Readiness predicate for the first half of diagonal-graph-equals-closure. -/
def concreteAnalyticSpineL2R2DiagonalGraphSubsetClosureReady : Prop :=
  concreteL2R2DiagonalGraphSubsetClosureGeneratedGraph ∧
  concreteAnalyticSpineL2R2ClosedOperatorTheoremReady ∧
  True ∧ True

/-- The R2 diagonal graph subset closure-generated graph theorem is ready. -/
theorem concrete_analytic_spine_l2_r2_diagonal_graph_subset_closure_ready :
    concreteAnalyticSpineL2R2DiagonalGraphSubsetClosureReady := by
  exact ⟨
    concrete_l2_r2_diagonal_graph_subset_closure_generated_graph,
    concrete_analytic_spine_l2_r2_closed_operator_theorem_ready,
    trivial,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
