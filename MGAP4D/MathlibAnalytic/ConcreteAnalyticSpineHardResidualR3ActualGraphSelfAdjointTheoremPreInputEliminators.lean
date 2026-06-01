import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualGraphSelfAdjointTheoremPreInput

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Elimination: actual-graph pre-input exposes the closed concrete R3 theorem inputs. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_preinput_closed_theorem_inputs
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphSelfAdjointTheoremPreInput G hG) :
    concreteAnalyticSpineHardResidualR3SelfAdjointTheoremInputsClosed := by
  rcases h with ⟨hclosed, _, _, _, _, _, _⟩
  exact hclosed

/-- Elimination: actual-graph pre-input exposes the transported formal self-adjoint surface. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_preinput_formal_transport
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphSelfAdjointTheoremPreInput G hG) :
    concreteAnalyticSpineHardResidualR3ActualGraphFormalSelfAdjointTransport G hG := by
  rcases h with ⟨_, htransport, _, _, _, _, _⟩
  exact htransport

/-- Elimination: actual-graph pre-input exposes actual graph = formal linear-map graph pointwise. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_preinput_iff_linear_map
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphSelfAdjointTheoremPreInput G hG) :
    ∀ p : ConcreteL2R2PairSpace,
      G p ↔ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph p := by
  rcases h with ⟨_, _, hlinear, _, _, _, _⟩
  exact hlinear

/-- Elimination: actual-graph pre-input exposes actual graph = formal candidate graph pointwise. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_preinput_iff_candidate
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphSelfAdjointTheoremPreInput G hG) :
    ∀ p : ConcreteL2R2PairSpace,
      G p ↔ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p := by
  rcases h with ⟨_, _, _, hcandidate, _, _, _⟩
  exact hcandidate

/-- Elimination: actual-graph pre-input exposes actual graph = completed graph carrier pointwise. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_preinput_iff_completed_graph
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphSelfAdjointTheoremPreInput G hG) :
    ∀ p : ConcreteL2R2PairSpace,
      G p ↔ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p := by
  rcases h with ⟨_, _, _, _, hcompleted, _, _⟩
  exact hcompleted

/-- Elimination: actual-graph pre-input exposes formal graph self-adjointness. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_preinput_formal_self_adjointness
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphSelfAdjointTheoremPreInput G hG) :
    concreteL2R4FormalGraphSelfAdjointness := by
  rcases h with ⟨_, _, _, _, _, hformal, _⟩
  exact hformal

/-- Elimination: actual-graph pre-input keeps the non-promotion boundary visible. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_preinput_boundary_not_self_adjointness
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphSelfAdjointTheoremPreInput G hG) :
    concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness := by
  rcases h with ⟨_, _, _, _, _, _, hboundary⟩
  exact hboundary

/-- Closed actual-graph theorem pre-input package.

This exposes every reusable component of the actual-graph pre-input without
unfolding the transport chain. -/
def concreteAnalyticSpineHardResidualR3ActualGraphSelfAdjointTheoremPreInputClosed
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) : Prop :=
  concreteAnalyticSpineHardResidualR3ActualGraphSelfAdjointTheoremPreInput G hG ∧
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

/-- The closed actual-graph theorem pre-input package is ready from the single
canonical-formal equality for `G`. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_graph_self_adjoint_theorem_preinput_closed_ready
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) :
    concreteAnalyticSpineHardResidualR3ActualGraphSelfAdjointTheoremPreInputClosed G hG := by
  let h := concrete_analytic_spine_hard_residual_r3_actual_graph_self_adjoint_theorem_preinput_ready G hG
  exact ⟨
    h,
    concrete_analytic_spine_hard_residual_r3_actual_preinput_closed_theorem_inputs G hG h,
    concrete_analytic_spine_hard_residual_r3_actual_preinput_formal_transport G hG h,
    concrete_analytic_spine_hard_residual_r3_actual_preinput_iff_linear_map G hG h,
    concrete_analytic_spine_hard_residual_r3_actual_preinput_iff_candidate G hG h,
    concrete_analytic_spine_hard_residual_r3_actual_preinput_iff_completed_graph G hG h,
    concrete_analytic_spine_hard_residual_r3_actual_preinput_formal_self_adjointness G hG h,
    concrete_analytic_spine_hard_residual_r3_actual_preinput_boundary_not_self_adjointness G hG h⟩

/-- R3 after actual-graph theorem pre-input eliminators: the actual graph `G`
can now be handed to the future Mathlib self-adjointness promotion theorem with
all graph and formal inputs named. -/
def concreteAnalyticSpineHardResidualR3AfterActualGraphSelfAdjointTheoremPreInputEliminators : Prop :=
  (∀ (G : ConcreteL2R2PairSpace → Prop)
      (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G),
    concreteAnalyticSpineHardResidualR3ActualGraphSelfAdjointTheoremPreInputClosed G hG) ∧
  concreteAnalyticSpineHardResidualR3AfterActualGraphSelfAdjointTheoremPreInput

/-- The post-actual-graph theorem pre-input eliminator surface is ready. -/
theorem concrete_analytic_spine_hard_residual_r3_after_actual_graph_self_adjoint_theorem_preinput_eliminators_ready :
    concreteAnalyticSpineHardResidualR3AfterActualGraphSelfAdjointTheoremPreInputEliminators := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_actual_graph_self_adjoint_theorem_preinput_closed_ready,
    concrete_analytic_spine_hard_residual_r3_after_actual_graph_self_adjoint_theorem_preinput_ready⟩

end

end MathlibAnalytic
end MGAP4D
