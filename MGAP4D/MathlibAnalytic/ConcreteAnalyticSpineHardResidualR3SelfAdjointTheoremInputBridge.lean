import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3SelfAdjointPromotionTarget

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The concrete theorem-input bridge for hard-residual R3.

This extracts, as reusable theorem inputs, the concrete formal graph facts that a
future Mathlib-compatible self-adjointness theorem must consume.  It is stronger
than a checklist: it exposes the carrier/candidate/linear-map graph equalities
and the formal graph-level self-adjointness statement as named inputs. -/
def concreteAnalyticSpineHardResidualR3SelfAdjointTheoremInputBridge : Prop :=
  concreteAnalyticSpineHardResidualR3SelfAdjointPromotionTargetReady ∧
  concreteAnalyticSpineHardResidualR3MathlibAdjointTransportTargetReady ∧
  concreteAnalyticSpineHardResidualR3MathlibAdjointGraphContract ∧
  concreteAnalyticSpineHardResidualR3FormalAdjointLinearMapGraphEqualsCandidate ∧
  concreteL2R4FormalGraphSelfAdjointness

/-- The concrete theorem-input bridge for hard-residual R3 is ready. -/
theorem concrete_analytic_spine_hard_residual_r3_self_adjoint_theorem_input_bridge_ready :
    concreteAnalyticSpineHardResidualR3SelfAdjointTheoremInputBridge := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_self_adjoint_promotion_surface_ready,
    concrete_analytic_spine_hard_residual_r3_mathlib_adjoint_transport_surface_ready,
    concrete_analytic_spine_hard_residual_r3_mathlib_adjoint_graph_contract_ready,
    concrete_analytic_spine_hard_residual_r3_formal_adjoint_linear_map_graph_eq_candidate,
    concrete_l2_r4_formal_graph_self_adjointness⟩

/-- Projection: the completed diagonal graph carrier is the formal adjoint graph candidate. -/
theorem concrete_analytic_spine_hard_residual_r3_graph_carrier_eq_formal_adjoint_candidate :
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier =
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  exact concrete_l2_r2_completed_diagonal_formal_adjoint_graph_agreement_handoff

/-- Projection: the formal adjoint linear-map graph is the formal adjoint graph candidate. -/
theorem concrete_analytic_spine_hard_residual_r3_linear_map_graph_eq_formal_adjoint_candidate :
    concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph =
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  exact concrete_analytic_spine_hard_residual_r3_formal_adjoint_linear_map_graph_eq_candidate

/-- Projection: the formal adjoint linear-map graph is the completed diagonal graph carrier. -/
theorem concrete_analytic_spine_hard_residual_r3_linear_map_graph_eq_completed_diagonal_graph :
    concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph =
      concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier := by
  ext p
  exact concrete_l2_r2_formal_adjoint_linear_map_graph_pointwise_agrees_completed_diagonal p

/-- Projection: hard-residual R3 has the formal graph-level self-adjointness input. -/
theorem concrete_analytic_spine_hard_residual_r3_has_formal_graph_self_adjointness :
    concreteL2R4FormalGraphSelfAdjointness := by
  exact concrete_l2_r4_formal_graph_self_adjointness

/-- R3 theorem-input bundle containing the three graph equalities in a single
transport-ready surface. -/
def concreteAnalyticSpineHardResidualR3GraphEqualityInputBundle : Prop :=
  (concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier =
    concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate) ∧
  (concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph =
    concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate) ∧
  (concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph =
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier)

/-- The R3 graph-equality input bundle is ready. -/
theorem concrete_analytic_spine_hard_residual_r3_graph_equality_input_bundle_ready :
    concreteAnalyticSpineHardResidualR3GraphEqualityInputBundle := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_graph_carrier_eq_formal_adjoint_candidate,
    concrete_analytic_spine_hard_residual_r3_linear_map_graph_eq_formal_adjoint_candidate,
    concrete_analytic_spine_hard_residual_r3_linear_map_graph_eq_completed_diagonal_graph⟩

/-- Final pre-theorem input surface for the future concrete Mathlib
self-adjointness theorem.  The remaining step is the actual Mathlib adjoint graph
identification and the promotion to the appropriate Mathlib self-adjointness
predicate. -/
def concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointTheoremPreInput : Prop :=
  concreteAnalyticSpineHardResidualR3SelfAdjointTheoremInputBridge ∧
  concreteAnalyticSpineHardResidualR3GraphEqualityInputBundle ∧
  concreteL2R4FormalGraphSelfAdjointness ∧
  concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness

/-- The concrete self-adjointness theorem pre-input surface is ready. -/
theorem concrete_analytic_spine_hard_residual_r3_concrete_self_adjoint_theorem_preinput_ready :
    concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointTheoremPreInput := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_self_adjoint_theorem_input_bridge_ready,
    concrete_analytic_spine_hard_residual_r3_graph_equality_input_bundle_ready,
    concrete_analytic_spine_hard_residual_r3_has_formal_graph_self_adjointness,
    concrete_l2_r2_closed_operator_boundary_not_self_adjointness⟩

/-- Elimination: the pre-input surface exposes the carrier/candidate graph equality. -/
theorem concrete_analytic_spine_hard_residual_r3_preinput_carrier_eq_candidate
    (h : concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointTheoremPreInput) :
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier =
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  rcases h with ⟨_, hgraph, _, _⟩
  exact hgraph.1

/-- Elimination: the pre-input surface exposes the linear-map/candidate graph equality. -/
theorem concrete_analytic_spine_hard_residual_r3_preinput_linear_map_eq_candidate
    (h : concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointTheoremPreInput) :
    concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph =
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  rcases h with ⟨_, hgraph, _, _⟩
  exact hgraph.2.1

/-- Elimination: the pre-input surface exposes the linear-map/completed-graph equality. -/
theorem concrete_analytic_spine_hard_residual_r3_preinput_linear_map_eq_completed_graph
    (h : concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointTheoremPreInput) :
    concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph =
      concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier := by
  rcases h with ⟨_, hgraph, _, _⟩
  exact hgraph.2.2

/-- Elimination: the pre-input surface exposes the formal graph self-adjointness fact. -/
theorem concrete_analytic_spine_hard_residual_r3_preinput_formal_graph_self_adjointness
    (h : concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointTheoremPreInput) :
    concreteL2R4FormalGraphSelfAdjointness := by
  rcases h with ⟨_, _, hformal, _⟩
  exact hformal

/-- Elimination: the pre-input surface still carries the non-promotion boundary. -/
theorem concrete_analytic_spine_hard_residual_r3_preinput_boundary_not_self_adjointness
    (h : concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointTheoremPreInput) :
    concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness := by
  rcases h with ⟨_, _, _, hboundary⟩
  exact hboundary

/-- Closed theorem-input package: the ready pre-input surface can be consumed
without re-opening any of the graph-equality proofs. -/
def concreteAnalyticSpineHardResidualR3SelfAdjointTheoremInputsClosed : Prop :=
  concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointTheoremPreInput ∧
  (concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier =
    concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate) ∧
  (concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph =
    concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate) ∧
  (concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph =
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier) ∧
  concreteL2R4FormalGraphSelfAdjointness ∧
  concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness

/-- The closed theorem-input package is ready. -/
theorem concrete_analytic_spine_hard_residual_r3_self_adjoint_theorem_inputs_closed_ready :
    concreteAnalyticSpineHardResidualR3SelfAdjointTheoremInputsClosed := by
  let h := concrete_analytic_spine_hard_residual_r3_concrete_self_adjoint_theorem_preinput_ready
  exact ⟨
    h,
    concrete_analytic_spine_hard_residual_r3_preinput_carrier_eq_candidate h,
    concrete_analytic_spine_hard_residual_r3_preinput_linear_map_eq_candidate h,
    concrete_analytic_spine_hard_residual_r3_preinput_linear_map_eq_completed_graph h,
    concrete_analytic_spine_hard_residual_r3_preinput_formal_graph_self_adjointness h,
    concrete_analytic_spine_hard_residual_r3_preinput_boundary_not_self_adjointness h⟩

end

end MathlibAnalytic
end MGAP4D
