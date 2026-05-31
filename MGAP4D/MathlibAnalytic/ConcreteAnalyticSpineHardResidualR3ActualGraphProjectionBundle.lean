import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphToCanonicalFormalSlot

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Projection bundle extracted from a future actual Mathlib adjoint graph.

Given one proof that the future actual Mathlib adjoint graph `G` agrees with the
canonical formal slot graph, this bundle exposes all graph equalities needed by
the self-adjointness promotion surface. -/
def concreteAnalyticSpineHardResidualR3ActualGraphProjectionBundle
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) : Prop :=
  (G = concreteAnalyticSpineHardResidualR3CanonicalFormalAdjointGraphSlot.mathlibAdjointGraph) ∧
  (G = concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph) ∧
  (G = concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate) ∧
  (G = concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier) ∧
  concreteL2R4FormalGraphSelfAdjointness

/-- Projection from actual graph to the formal adjoint linear-map graph. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_graph_eq_formal_linear_map
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) :
    G = concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph := by
  exact concrete_analytic_spine_hard_residual_r3_actual_graph_identifies_formal_linear_map G hG

/-- Projection from actual graph to the formal adjoint candidate graph. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_graph_eq_candidate
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) :
    G = concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  exact concrete_analytic_spine_hard_residual_r3_abstract_mathlib_graph_eq_candidate G
    (concrete_analytic_spine_hard_residual_r3_actual_graph_identifies_formal_linear_map G hG)

/-- Projection from actual graph to the completed diagonal graph carrier. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_graph_eq_completed_graph
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) :
    G = concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier := by
  exact concrete_analytic_spine_hard_residual_r3_abstract_mathlib_graph_eq_completed_graph G
    (concrete_analytic_spine_hard_residual_r3_actual_graph_identifies_formal_linear_map G hG)

/-- The projection bundle is ready from the single canonical-formal equality. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_graph_projection_bundle_ready
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) :
    concreteAnalyticSpineHardResidualR3ActualGraphProjectionBundle G hG := by
  exact ⟨
    hG,
    concrete_analytic_spine_hard_residual_r3_actual_graph_eq_formal_linear_map G hG,
    concrete_analytic_spine_hard_residual_r3_actual_graph_eq_candidate G hG,
    concrete_analytic_spine_hard_residual_r3_actual_graph_eq_completed_graph G hG,
    concrete_l2_r4_formal_graph_self_adjointness⟩

/-- Final graph-input package for the future actual Mathlib graph.

This surface contains both the conditional promotion package and all graph
projection equalities, so a later self-adjointness theorem can consume one
package rather than re-opening the adapter chain. -/
def concreteAnalyticSpineHardResidualR3ActualGraphFinalInputPackage
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) : Prop :=
  concreteAnalyticSpineHardResidualR3ActualGraphConditionalPromotionPackage G hG ∧
  concreteAnalyticSpineHardResidualR3ActualGraphProjectionBundle G hG ∧
  concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness

/-- The final graph-input package is ready from the single canonical-formal equality. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_graph_final_input_package_ready
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) :
    concreteAnalyticSpineHardResidualR3ActualGraphFinalInputPackage G hG := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_actual_graph_conditional_promotion_package_ready G hG,
    concrete_analytic_spine_hard_residual_r3_actual_graph_projection_bundle_ready G hG,
    concrete_l2_r2_closed_operator_boundary_not_self_adjointness⟩

/-- R3 after the actual-graph projection bundle: the only remaining executable
implementation task is to instantiate `G` by the actual Mathlib adjoint graph and
supply its canonical-formal equality proof. -/
def concreteAnalyticSpineHardResidualR3AfterActualGraphProjectionBundle : Prop :=
  (∀ (G : ConcreteL2R2PairSpace → Prop)
      (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G),
    concreteAnalyticSpineHardResidualR3ActualGraphFinalInputPackage G hG) ∧
  concreteAnalyticSpineHardResidualR3ActualGraphToCanonicalFormalBridgeReady

/-- The post-actual-graph projection bundle surface is ready. -/
theorem concrete_analytic_spine_hard_residual_r3_after_actual_graph_projection_bundle_ready :
    concreteAnalyticSpineHardResidualR3AfterActualGraphProjectionBundle := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_actual_graph_final_input_package_ready,
    concrete_analytic_spine_hard_residual_r3_actual_graph_to_canonical_formal_bridge_ready⟩

end

end MathlibAnalytic
end MGAP4D
