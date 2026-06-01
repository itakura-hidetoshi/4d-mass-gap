import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualGraphMembershipSummary

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Transported formal graph-level self-adjointness surface for a future actual
Mathlib adjoint graph predicate.

This does not assert Mathlib `IsSelfAdjoint`.  It says that once the actual
Mathlib graph predicate `G` is identified with the canonical formal graph, the
already proved R4 formal graph self-adjointness inputs and the pointwise graph
transports are available together. -/
def concreteAnalyticSpineHardResidualR3ActualGraphFormalSelfAdjointTransport
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) : Prop :=
  concreteAnalyticSpineHardResidualR3ActualGraphMembershipSummary G hG ∧
  (∀ p : ConcreteL2R2PairSpace,
    G p ↔ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph p) ∧
  (∀ p : ConcreteL2R2PairSpace,
    G p ↔ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p) ∧
  (∀ p : ConcreteL2R2PairSpace,
    G p ↔ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p) ∧
  concreteL2R4FormalGraphSelfAdjointness ∧
  concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness

/-- Elimination: membership summary exposes the formal linear-map graph iff. -/
theorem concrete_analytic_spine_hard_residual_r3_membership_summary_iff_formal_linear_map
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphMembershipSummary G hG) :
    ∀ p : ConcreteL2R2PairSpace,
      G p ↔ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph p := by
  rcases h with ⟨_, hlinear, _, _, _, _, _, _⟩
  exact hlinear

/-- Elimination: membership summary exposes the formal candidate graph iff. -/
theorem concrete_analytic_spine_hard_residual_r3_membership_summary_iff_candidate
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphMembershipSummary G hG) :
    ∀ p : ConcreteL2R2PairSpace,
      G p ↔ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p := by
  rcases h with ⟨_, _, hcandidate, _, _, _, _, _⟩
  exact hcandidate

/-- Elimination: membership summary exposes the completed graph carrier iff. -/
theorem concrete_analytic_spine_hard_residual_r3_membership_summary_iff_completed_graph
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphMembershipSummary G hG) :
    ∀ p : ConcreteL2R2PairSpace,
      G p ↔ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p := by
  rcases h with ⟨_, _, _, hcompleted, _, _, _, _⟩
  exact hcompleted

/-- The transported formal graph-level self-adjointness surface is ready from a
single canonical-formal equality for the future actual Mathlib graph. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_graph_formal_self_adjoint_transport_ready
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) :
    concreteAnalyticSpineHardResidualR3ActualGraphFormalSelfAdjointTransport G hG := by
  let hsummary := concrete_analytic_spine_hard_residual_r3_actual_graph_membership_summary_ready G hG
  exact ⟨
    hsummary,
    concrete_analytic_spine_hard_residual_r3_membership_summary_iff_formal_linear_map G hG hsummary,
    concrete_analytic_spine_hard_residual_r3_membership_summary_iff_candidate G hG hsummary,
    concrete_analytic_spine_hard_residual_r3_membership_summary_iff_completed_graph G hG hsummary,
    concrete_l2_r4_formal_graph_self_adjointness,
    concrete_l2_r2_closed_operator_boundary_not_self_adjointness⟩

/-- R3 after transporting formal graph-level self-adjointness to a future actual
Mathlib graph predicate.  The remaining task is still not hidden: instantiate the
actual Mathlib adjoint graph and then perform the genuine Mathlib self-adjointness
promotion. -/
def concreteAnalyticSpineHardResidualR3AfterActualGraphFormalSelfAdjointTransport : Prop :=
  (∀ (G : ConcreteL2R2PairSpace → Prop)
      (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G),
    concreteAnalyticSpineHardResidualR3ActualGraphFormalSelfAdjointTransport G hG) ∧
  concreteAnalyticSpineHardResidualR3AfterMembershipSummary

/-- The post-actual-graph formal self-adjoint transport surface is ready. -/
theorem concrete_analytic_spine_hard_residual_r3_after_actual_graph_formal_self_adjoint_transport_ready :
    concreteAnalyticSpineHardResidualR3AfterActualGraphFormalSelfAdjointTransport := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_actual_graph_formal_self_adjoint_transport_ready,
    concrete_analytic_spine_hard_residual_r3_after_membership_summary_ready⟩

end

end MathlibAnalytic
end MGAP4D
