import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3CanonicalFormalAdjointGraphSlot

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- External identification input for the actual Mathlib adjoint graph.

The next concrete Mathlib implementation only has to supply a graph predicate
`G` and prove that it is the same predicate as the canonical formal slot graph.
This is deliberately weaker than declaring `G` to be self-adjoint; it is only the
graph-identification input. -/
def concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal
    (G : ConcreteL2R2PairSpace → Prop) : Prop :=
  G = concreteAnalyticSpineHardResidualR3CanonicalFormalAdjointGraphSlot.mathlibAdjointGraph

/-- From identification with the canonical formal slot, obtain identification
with the concrete formal adjoint linear-map graph. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_graph_identifies_formal_linear_map
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) :
    concreteAnalyticSpineHardResidualR3AbstractMathlibAdjointGraphIdentification G := by
  unfold concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal at hG
  unfold concreteAnalyticSpineHardResidualR3AbstractMathlibAdjointGraphIdentification
  rw [hG]
  exact concrete_analytic_spine_hard_residual_r3_canonical_formal_slot_graph_eq_linear_map_graph

/-- A graph identified with the canonical formal slot fills the R3 Mathlib
adjoint graph slot. -/
def concreteAnalyticSpineHardResidualR3ActualMathlibGraphSlot
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) :
    ConcreteAnalyticSpineHardResidualR3MathlibAdjointGraphSlot where
  mathlibAdjointGraph := G
  identifiesFormalAdjointGraph :=
    concrete_analytic_spine_hard_residual_r3_actual_graph_identifies_formal_linear_map G hG

/-- The actual graph slot exports the graph equality to the canonical formal slot. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_graph_slot_eq_canonical_formal
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) :
    (concreteAnalyticSpineHardResidualR3ActualMathlibGraphSlot G hG).mathlibAdjointGraph =
      concreteAnalyticSpineHardResidualR3CanonicalFormalAdjointGraphSlot.mathlibAdjointGraph := by
  exact hG

/-- The actual graph slot exports the graph equality to the formal adjoint linear-map graph. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_graph_slot_eq_formal_linear_map
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) :
    (concreteAnalyticSpineHardResidualR3ActualMathlibGraphSlot G hG).mathlibAdjointGraph =
      concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph := by
  change G = concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph
  exact concrete_analytic_spine_hard_residual_r3_actual_graph_identifies_formal_linear_map G hG

/-- The actual graph slot yields the slot-level promotion package. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_graph_slot_promotion_package_ready
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) :
    concreteAnalyticSpineHardResidualR3SlotLevelSelfAdjointPromotionPackage
      (concreteAnalyticSpineHardResidualR3ActualMathlibGraphSlot G hG) := by
  exact concrete_analytic_spine_hard_residual_r3_slot_level_self_adjoint_promotion_package_ready
    (concreteAnalyticSpineHardResidualR3ActualMathlibGraphSlot G hG)

/-- Conditional promotion package from a future actual Mathlib graph predicate. -/
def concreteAnalyticSpineHardResidualR3ActualGraphConditionalPromotionPackage
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) : Prop :=
  concreteAnalyticSpineHardResidualR3SlotLevelSelfAdjointPromotionPackage
    (concreteAnalyticSpineHardResidualR3ActualMathlibGraphSlot G hG) ∧
  ((concreteAnalyticSpineHardResidualR3ActualMathlibGraphSlot G hG).mathlibAdjointGraph =
    concreteAnalyticSpineHardResidualR3CanonicalFormalAdjointGraphSlot.mathlibAdjointGraph) ∧
  ((concreteAnalyticSpineHardResidualR3ActualMathlibGraphSlot G hG).mathlibAdjointGraph =
    concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph) ∧
  concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness

/-- The conditional promotion package is ready from one canonical-formal graph equality. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_graph_conditional_promotion_package_ready
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) :
    concreteAnalyticSpineHardResidualR3ActualGraphConditionalPromotionPackage G hG := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_actual_graph_slot_promotion_package_ready G hG,
    concrete_analytic_spine_hard_residual_r3_actual_graph_slot_eq_canonical_formal G hG,
    concrete_analytic_spine_hard_residual_r3_actual_graph_slot_eq_formal_linear_map G hG,
    concrete_l2_r2_closed_operator_boundary_not_self_adjointness⟩

/-- After this bridge, the future implementation task is exactly to define the
actual Mathlib adjoint graph predicate and prove its equality with the canonical
formal slot graph. -/
def concreteAnalyticSpineHardResidualR3ActualGraphToCanonicalFormalBridgeReady : Prop :=
  (∀ (G : ConcreteL2R2PairSpace → Prop)
      (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G),
    concreteAnalyticSpineHardResidualR3ActualGraphConditionalPromotionPackage G hG) ∧
  concreteAnalyticSpineHardResidualR3AfterCanonicalFormalSlotBlocker

/-- The actual-graph-to-canonical-formal bridge is ready. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_graph_to_canonical_formal_bridge_ready :
    concreteAnalyticSpineHardResidualR3ActualGraphToCanonicalFormalBridgeReady := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_actual_graph_conditional_promotion_package_ready,
    concrete_analytic_spine_hard_residual_r3_after_canonical_formal_slot_blocker_visible⟩

end

end MathlibAnalytic
end MGAP4D
