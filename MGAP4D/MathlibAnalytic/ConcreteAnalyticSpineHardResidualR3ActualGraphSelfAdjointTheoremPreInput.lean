import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualGraphFormalSelfAdjointTransport
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3SelfAdjointTheoremInputBridge

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Actual-graph theorem pre-input surface.

This combines the already closed concrete R3 self-adjoint theorem inputs with the
transported formal graph-level self-adjointness surface for a future actual
Mathlib adjoint graph predicate `G`.  It still does not assert Mathlib
`IsSelfAdjoint`; it is the pre-input package consumed immediately before that
promotion. -/
def concreteAnalyticSpineHardResidualR3ActualGraphSelfAdjointTheoremPreInput
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) : Prop :=
  concreteAnalyticSpineHardResidualR3SelfAdjointTheoremInputsClosed ∧
  concreteAnalyticSpineHardResidualR3ActualGraphFormalSelfAdjointTransport G hG ∧
  (∀ p : ConcreteL2R2PairSpace,
    G p ↔ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph p) ∧
  (∀ p : ConcreteL2R2PairSpace,
    G p ↔ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p) ∧
  (∀ p : ConcreteL2R2PairSpace,
    G p ↔ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p) ∧
  concreteL2R4FormalGraphSelfAdjointness ∧
  concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness

/-- Elimination: transported formal self-adjointness exposes actual graph =
formal linear-map graph pointwise. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_formal_transport_iff_linear_map
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphFormalSelfAdjointTransport G hG) :
    ∀ p : ConcreteL2R2PairSpace,
      G p ↔ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph p := by
  rcases h with ⟨_, hlinear, _, _, _, _⟩
  exact hlinear

/-- Elimination: transported formal self-adjointness exposes actual graph =
formal candidate graph pointwise. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_formal_transport_iff_candidate
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphFormalSelfAdjointTransport G hG) :
    ∀ p : ConcreteL2R2PairSpace,
      G p ↔ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p := by
  rcases h with ⟨_, _, hcandidate, _, _, _⟩
  exact hcandidate

/-- Elimination: transported formal self-adjointness exposes actual graph =
completed graph carrier pointwise. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_formal_transport_iff_completed_graph
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphFormalSelfAdjointTransport G hG) :
    ∀ p : ConcreteL2R2PairSpace,
      G p ↔ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p := by
  rcases h with ⟨_, _, _, hcompleted, _, _⟩
  exact hcompleted

/-- Elimination: transported formal self-adjointness exposes the formal graph
self-adjointness input. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_formal_transport_formal_self_adjointness
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphFormalSelfAdjointTransport G hG) :
    concreteL2R4FormalGraphSelfAdjointness := by
  rcases h with ⟨_, _, _, _, hformal, _⟩
  exact hformal

/-- Elimination: transported formal self-adjointness keeps the non-promotion
boundary visible. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_formal_transport_boundary_not_self_adjointness
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphFormalSelfAdjointTransport G hG) :
    concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness := by
  rcases h with ⟨_, _, _, _, _, hboundary⟩
  exact hboundary

/-- The actual-graph self-adjoint theorem pre-input is ready from the single
canonical-formal equality for `G`. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_graph_self_adjoint_theorem_preinput_ready
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) :
    concreteAnalyticSpineHardResidualR3ActualGraphSelfAdjointTheoremPreInput G hG := by
  let htransport :=
    concrete_analytic_spine_hard_residual_r3_actual_graph_formal_self_adjoint_transport_ready G hG
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_self_adjoint_theorem_inputs_closed_ready,
    htransport,
    concrete_analytic_spine_hard_residual_r3_actual_formal_transport_iff_linear_map G hG htransport,
    concrete_analytic_spine_hard_residual_r3_actual_formal_transport_iff_candidate G hG htransport,
    concrete_analytic_spine_hard_residual_r3_actual_formal_transport_iff_completed_graph G hG htransport,
    concrete_analytic_spine_hard_residual_r3_actual_formal_transport_formal_self_adjointness G hG htransport,
    concrete_analytic_spine_hard_residual_r3_actual_formal_transport_boundary_not_self_adjointness G hG htransport⟩

/-- R3 after actual-graph self-adjoint theorem pre-input: all graph and formal
self-adjointness inputs are now available for a future actual Mathlib graph `G`,
while the genuine Mathlib self-adjointness promotion remains explicit. -/
def concreteAnalyticSpineHardResidualR3AfterActualGraphSelfAdjointTheoremPreInput : Prop :=
  (∀ (G : ConcreteL2R2PairSpace → Prop)
      (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G),
    concreteAnalyticSpineHardResidualR3ActualGraphSelfAdjointTheoremPreInput G hG) ∧
  concreteAnalyticSpineHardResidualR3AfterActualGraphFormalSelfAdjointTransport

/-- The post-actual-graph self-adjoint theorem pre-input surface is ready. -/
theorem concrete_analytic_spine_hard_residual_r3_after_actual_graph_self_adjoint_theorem_preinput_ready :
    concreteAnalyticSpineHardResidualR3AfterActualGraphSelfAdjointTheoremPreInput := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_actual_graph_self_adjoint_theorem_preinput_ready,
    concrete_analytic_spine_hard_residual_r3_after_actual_graph_formal_self_adjoint_transport_ready⟩

end

end MathlibAnalytic
end MGAP4D
