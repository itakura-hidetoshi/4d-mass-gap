import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualGraphFinalInputEliminators

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Membership transport from the future actual Mathlib adjoint graph to the
canonical formal slot graph. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_graph_mem_iff_canonical_formal
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphFinalEliminatorPackage G hG)
    (p : ConcreteL2R2PairSpace) :
    G p ↔ concreteAnalyticSpineHardResidualR3CanonicalFormalAdjointGraphSlot.mathlibAdjointGraph p := by
  rcases h with ⟨_, _, hcanonical, _, _, _, _, _⟩
  rw [hcanonical]

/-- Membership transport from the future actual Mathlib adjoint graph to the
formal adjoint linear-map graph. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_graph_mem_iff_formal_linear_map
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphFinalEliminatorPackage G hG)
    (p : ConcreteL2R2PairSpace) :
    G p ↔ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph p := by
  rcases h with ⟨_, _, _, hlinear, _, _, _, _⟩
  rw [hlinear]

/-- Membership transport from the future actual Mathlib adjoint graph to the
formal adjoint candidate graph. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_graph_mem_iff_candidate
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphFinalEliminatorPackage G hG)
    (p : ConcreteL2R2PairSpace) :
    G p ↔ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p := by
  rcases h with ⟨_, _, _, _, hcandidate, _, _, _⟩
  rw [hcandidate]

/-- Membership transport from the future actual Mathlib adjoint graph to the
completed diagonal graph carrier. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_graph_mem_iff_completed_graph
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphFinalEliminatorPackage G hG)
    (p : ConcreteL2R2PairSpace) :
    G p ↔ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p := by
  rcases h with ⟨_, _, _, _, _, hcompleted, _, _⟩
  rw [hcompleted]

/-- Actual graph is included in the completed diagonal graph carrier. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_graph_subset_completed_graph
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphFinalEliminatorPackage G hG) :
    ∀ p : ConcreteL2R2PairSpace,
      G p → concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p := by
  intro p hp
  exact (concrete_analytic_spine_hard_residual_r3_actual_graph_mem_iff_completed_graph
    G hG h p).mp hp

/-- Completed diagonal graph carrier is included in the actual graph. -/
theorem concrete_analytic_spine_hard_residual_r3_completed_graph_subset_actual_graph
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphFinalEliminatorPackage G hG) :
    ∀ p : ConcreteL2R2PairSpace,
      concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p → G p := by
  intro p hp
  exact (concrete_analytic_spine_hard_residual_r3_actual_graph_mem_iff_completed_graph
    G hG h p).mpr hp

/-- Actual graph is included in the formal adjoint candidate graph. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_graph_subset_candidate
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphFinalEliminatorPackage G hG) :
    ∀ p : ConcreteL2R2PairSpace,
      G p → concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p := by
  intro p hp
  exact (concrete_analytic_spine_hard_residual_r3_actual_graph_mem_iff_candidate
    G hG h p).mp hp

/-- Formal adjoint candidate graph is included in the actual graph. -/
theorem concrete_analytic_spine_hard_residual_r3_candidate_subset_actual_graph
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphFinalEliminatorPackage G hG) :
    ∀ p : ConcreteL2R2PairSpace,
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p → G p := by
  intro p hp
  exact (concrete_analytic_spine_hard_residual_r3_actual_graph_mem_iff_candidate
    G hG h p).mpr hp

/-- Membership transport package for a future actual Mathlib adjoint graph. -/
def concreteAnalyticSpineHardResidualR3ActualGraphMembershipTransportPackage
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) : Prop :=
  concreteAnalyticSpineHardResidualR3ActualGraphFinalEliminatorPackage G hG ∧
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

/-- The membership transport package is ready from the final eliminator package. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_graph_membership_transport_package_ready
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) :
    concreteAnalyticSpineHardResidualR3ActualGraphMembershipTransportPackage G hG := by
  let h := concrete_analytic_spine_hard_residual_r3_actual_graph_final_eliminator_package_ready G hG
  exact ⟨
    h,
    concrete_analytic_spine_hard_residual_r3_actual_graph_mem_iff_formal_linear_map G hG h,
    concrete_analytic_spine_hard_residual_r3_actual_graph_mem_iff_candidate G hG h,
    concrete_analytic_spine_hard_residual_r3_actual_graph_mem_iff_completed_graph G hG h,
    concrete_analytic_spine_hard_residual_r3_actual_graph_subset_completed_graph G hG h,
    concrete_analytic_spine_hard_residual_r3_completed_graph_subset_actual_graph G hG h,
    concrete_analytic_spine_hard_residual_r3_actual_graph_subset_candidate G hG h,
    concrete_analytic_spine_hard_residual_r3_candidate_subset_actual_graph G hG h⟩

/-- R3 after membership transport: graph equality, pointwise membership, and
bidirectional containment have all been transported to a future actual Mathlib
adjoint graph once its canonical-formal equality is supplied. -/
def concreteAnalyticSpineHardResidualR3AfterMembershipTransport : Prop :=
  (∀ (G : ConcreteL2R2PairSpace → Prop)
      (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G),
    concreteAnalyticSpineHardResidualR3ActualGraphMembershipTransportPackage G hG) ∧
  concreteAnalyticSpineHardResidualR3AfterFinalInputEliminators

/-- The post-membership-transport R3 surface is ready. -/
theorem concrete_analytic_spine_hard_residual_r3_after_membership_transport_ready :
    concreteAnalyticSpineHardResidualR3AfterMembershipTransport := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_actual_graph_membership_transport_package_ready,
    concrete_analytic_spine_hard_residual_r3_after_final_input_eliminators_ready⟩

end

end MathlibAnalytic
end MGAP4D
