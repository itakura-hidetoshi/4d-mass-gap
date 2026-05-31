import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualGraphMembershipTransport

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Elimination: the membership transport package exposes the final eliminator package. -/
theorem concrete_analytic_spine_hard_residual_r3_membership_package_final_eliminator
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphMembershipTransportPackage G hG) :
    concreteAnalyticSpineHardResidualR3ActualGraphFinalEliminatorPackage G hG := by
  rcases h with ⟨hfinal, _, _, _, _, _, _, _⟩
  exact hfinal

/-- Elimination: actual graph membership is equivalent to the formal linear-map graph. -/
theorem concrete_analytic_spine_hard_residual_r3_membership_package_iff_formal_linear_map
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphMembershipTransportPackage G hG) :
    ∀ p : ConcreteL2R2PairSpace,
      G p ↔ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph p := by
  rcases h with ⟨_, hlinear, _, _, _, _, _, _⟩
  exact hlinear

/-- Elimination: actual graph membership is equivalent to the formal candidate graph. -/
theorem concrete_analytic_spine_hard_residual_r3_membership_package_iff_candidate
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphMembershipTransportPackage G hG) :
    ∀ p : ConcreteL2R2PairSpace,
      G p ↔ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p := by
  rcases h with ⟨_, _, hcandidate, _, _, _, _, _⟩
  exact hcandidate

/-- Elimination: actual graph membership is equivalent to the completed graph carrier. -/
theorem concrete_analytic_spine_hard_residual_r3_membership_package_iff_completed_graph
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphMembershipTransportPackage G hG) :
    ∀ p : ConcreteL2R2PairSpace,
      G p ↔ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p := by
  rcases h with ⟨_, _, _, hcompleted, _, _, _, _⟩
  exact hcompleted

/-- Elimination: actual graph implies completed graph carrier. -/
theorem concrete_analytic_spine_hard_residual_r3_membership_package_actual_to_completed
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphMembershipTransportPackage G hG) :
    ∀ p : ConcreteL2R2PairSpace,
      G p → concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p := by
  rcases h with ⟨_, _, _, _, hactualCompleted, _, _, _⟩
  exact hactualCompleted

/-- Elimination: completed graph carrier implies actual graph. -/
theorem concrete_analytic_spine_hard_residual_r3_membership_package_completed_to_actual
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphMembershipTransportPackage G hG) :
    ∀ p : ConcreteL2R2PairSpace,
      concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p → G p := by
  rcases h with ⟨_, _, _, _, _, hcompletedActual, _, _⟩
  exact hcompletedActual

/-- Elimination: actual graph implies candidate graph. -/
theorem concrete_analytic_spine_hard_residual_r3_membership_package_actual_to_candidate
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphMembershipTransportPackage G hG) :
    ∀ p : ConcreteL2R2PairSpace,
      G p → concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p := by
  rcases h with ⟨_, _, _, _, _, _, hactualCandidate, _⟩
  exact hactualCandidate

/-- Elimination: candidate graph implies actual graph. -/
theorem concrete_analytic_spine_hard_residual_r3_membership_package_candidate_to_actual
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphMembershipTransportPackage G hG) :
    ∀ p : ConcreteL2R2PairSpace,
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p → G p := by
  rcases h with ⟨_, _, _, _, _, _, _, hcandidateActual⟩
  exact hcandidateActual

/-- Membership summary package: all pointwise graph equivalences and directional
implications are exposed from the transported actual graph package. -/
def concreteAnalyticSpineHardResidualR3ActualGraphMembershipSummary
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) : Prop :=
  concreteAnalyticSpineHardResidualR3ActualGraphMembershipTransportPackage G hG ∧
  (∀ p : ConcreteL2R2PairSpace,
    G p ↔ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph p) ∧
  (∀ p : ConcreteL2R2PairSpace,
    G p ↔ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p) ∧
  (∀ p : ConcreteL2R2PairSpace,
    G p ↔ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p) ∧
  (∀ p : ConcreteL2R2PairSpace,
    G p → concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p) ∧
  (∀ p : ConcreteL2R2PairSpace,
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p → G p) ∧
  (∀ p : ConcreteL2R2PairSpace,
    G p → concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p) ∧
  (∀ p : ConcreteL2R2PairSpace,
    concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p → G p)

/-- The membership summary package is ready. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_graph_membership_summary_ready
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) :
    concreteAnalyticSpineHardResidualR3ActualGraphMembershipSummary G hG := by
  let h := concrete_analytic_spine_hard_residual_r3_actual_graph_membership_transport_package_ready G hG
  exact ⟨
    h,
    concrete_analytic_spine_hard_residual_r3_membership_package_iff_formal_linear_map G hG h,
    concrete_analytic_spine_hard_residual_r3_membership_package_iff_candidate G hG h,
    concrete_analytic_spine_hard_residual_r3_membership_package_iff_completed_graph G hG h,
    concrete_analytic_spine_hard_residual_r3_membership_package_actual_to_completed G hG h,
    concrete_analytic_spine_hard_residual_r3_membership_package_completed_to_actual G hG h,
    concrete_analytic_spine_hard_residual_r3_membership_package_actual_to_candidate G hG h,
    concrete_analytic_spine_hard_residual_r3_membership_package_candidate_to_actual G hG h⟩

/-- R3 after membership summary: the actual graph has been transported to all
concrete graph predicates pointwise, with no use of set-style membership on bare
predicates. -/
def concreteAnalyticSpineHardResidualR3AfterMembershipSummary : Prop :=
  (∀ (G : ConcreteL2R2PairSpace → Prop)
      (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G),
    concreteAnalyticSpineHardResidualR3ActualGraphMembershipSummary G hG) ∧
  concreteAnalyticSpineHardResidualR3AfterMembershipTransport

/-- The post-membership-summary R3 surface is ready. -/
theorem concrete_analytic_spine_hard_residual_r3_after_membership_summary_ready :
    concreteAnalyticSpineHardResidualR3AfterMembershipSummary := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_actual_graph_membership_summary_ready,
    concrete_analytic_spine_hard_residual_r3_after_membership_transport_ready⟩

end

end MathlibAnalytic
end MGAP4D
