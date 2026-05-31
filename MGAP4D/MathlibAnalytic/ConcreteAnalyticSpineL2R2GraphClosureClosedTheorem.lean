import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDensityTargetRefinement

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Closedness of the graph-norm closure carrier. -/
def concreteL2R2GraphClosureClosedTheorem : Prop :=
  @IsClosed ConcreteL2GraphPairSpace concreteL2GraphNormTopology
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget

/-- The graph-norm closure carrier is closed by `isClosed_closure`. -/
theorem concrete_l2_r2_graph_norm_closure_carrier_closed :
    concreteL2R2GraphClosureClosedTheorem := by
  unfold concreteL2R2GraphClosureClosedTheorem
  unfold concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget
  exact @isClosed_closure ConcreteL2GraphPairSpace concreteL2GraphNormTopology
    ConcreteL2FiniteSupportCoreGraphCarrier

/-- Readiness predicate for the R2 graph-norm closure closed theorem.

This is now a theorem-level readiness marker only: the closedness result itself
is the promoted content.  Later files may use it to prove closedness of the
completed diagonal graph once the equality with this closure carrier is proved. -/
def concreteL2R2GraphClosureClosedTheoremReady : Prop :=
  concreteL2R2GraphClosureClosedTheorem

/-- The R2 graph-norm closure carrier closed theorem is ready. -/
theorem concrete_analytic_spine_l2_r2_graph_closure_closed_theorem_ready :
    concreteL2R2GraphClosureClosedTheoremReady := by
  exact concrete_l2_r2_graph_norm_closure_carrier_closed

end

end MathlibAnalytic
end MGAP4D
