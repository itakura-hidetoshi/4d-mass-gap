import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualGraphProjectionBundle

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Elimination: the actual graph final input package exposes the conditional
promotion package. -/
theorem concrete_analytic_spine_hard_residual_r3_final_input_conditional_promotion
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphFinalInputPackage G hG) :
    concreteAnalyticSpineHardResidualR3ActualGraphConditionalPromotionPackage G hG := by
  rcases h with ⟨hpromotion, _, _⟩
  exact hpromotion

/-- Elimination: the actual graph final input package exposes the graph
projection bundle. -/
theorem concrete_analytic_spine_hard_residual_r3_final_input_projection_bundle
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphFinalInputPackage G hG) :
    concreteAnalyticSpineHardResidualR3ActualGraphProjectionBundle G hG := by
  rcases h with ⟨_, hprojection, _⟩
  exact hprojection

/-- Elimination: the actual graph final input package keeps the non-promotion
boundary visible. -/
theorem concrete_analytic_spine_hard_residual_r3_final_input_boundary_not_self_adjointness
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphFinalInputPackage G hG) :
    concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness := by
  rcases h with ⟨_, _, hboundary⟩
  exact hboundary

/-- Elimination: the projection bundle exposes actual graph = canonical formal graph. -/
theorem concrete_analytic_spine_hard_residual_r3_projection_bundle_eq_canonical_formal
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphProjectionBundle G hG) :
    G = concreteAnalyticSpineHardResidualR3CanonicalFormalAdjointGraphSlot.mathlibAdjointGraph := by
  rcases h with ⟨hcanonical, _, _, _, _⟩
  exact hcanonical

/-- Elimination: the projection bundle exposes actual graph = formal linear-map graph. -/
theorem concrete_analytic_spine_hard_residual_r3_projection_bundle_eq_formal_linear_map
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphProjectionBundle G hG) :
    G = concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph := by
  rcases h with ⟨_, hlinear, _, _, _⟩
  exact hlinear

/-- Elimination: the projection bundle exposes actual graph = candidate graph. -/
theorem concrete_analytic_spine_hard_residual_r3_projection_bundle_eq_candidate
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphProjectionBundle G hG) :
    G = concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  rcases h with ⟨_, _, hcandidate, _, _⟩
  exact hcandidate

/-- Elimination: the projection bundle exposes actual graph = completed graph carrier. -/
theorem concrete_analytic_spine_hard_residual_r3_projection_bundle_eq_completed_graph
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphProjectionBundle G hG) :
    G = concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier := by
  rcases h with ⟨_, _, _, hcompleted, _⟩
  exact hcompleted

/-- Elimination: the projection bundle exposes the formal graph self-adjointness
input. -/
theorem concrete_analytic_spine_hard_residual_r3_projection_bundle_formal_graph_self_adjointness
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G)
    (h : concreteAnalyticSpineHardResidualR3ActualGraphProjectionBundle G hG) :
    concreteL2R4FormalGraphSelfAdjointness := by
  rcases h with ⟨_, _, _, _, hformal⟩
  exact hformal

/-- Final eliminator package: after supplying the future actual Mathlib graph
and its canonical-formal equality proof, all promotion inputs are available
without unfolding the adapter chain. -/
def concreteAnalyticSpineHardResidualR3ActualGraphFinalEliminatorPackage
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) : Prop :=
  concreteAnalyticSpineHardResidualR3ActualGraphFinalInputPackage G hG ∧
  concreteAnalyticSpineHardResidualR3ActualGraphConditionalPromotionPackage G hG ∧
  (G = concreteAnalyticSpineHardResidualR3CanonicalFormalAdjointGraphSlot.mathlibAdjointGraph) ∧
  (G = concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph) ∧
  (G = concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate) ∧
  (G = concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier) ∧
  concreteL2R4FormalGraphSelfAdjointness ∧
  concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness

/-- The final eliminator package is ready from the single canonical-formal
equality proof for the future actual Mathlib graph. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_graph_final_eliminator_package_ready
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) :
    concreteAnalyticSpineHardResidualR3ActualGraphFinalEliminatorPackage G hG := by
  let hfinal := concrete_analytic_spine_hard_residual_r3_actual_graph_final_input_package_ready G hG
  let hprojection :=
    concrete_analytic_spine_hard_residual_r3_final_input_projection_bundle G hG hfinal
  exact ⟨
    hfinal,
    concrete_analytic_spine_hard_residual_r3_final_input_conditional_promotion G hG hfinal,
    concrete_analytic_spine_hard_residual_r3_projection_bundle_eq_canonical_formal G hG hprojection,
    concrete_analytic_spine_hard_residual_r3_projection_bundle_eq_formal_linear_map G hG hprojection,
    concrete_analytic_spine_hard_residual_r3_projection_bundle_eq_candidate G hG hprojection,
    concrete_analytic_spine_hard_residual_r3_projection_bundle_eq_completed_graph G hG hprojection,
    concrete_analytic_spine_hard_residual_r3_projection_bundle_formal_graph_self_adjointness G hG hprojection,
    concrete_analytic_spine_hard_residual_r3_final_input_boundary_not_self_adjointness G hG hfinal⟩

/-- R3 after final input eliminators: the remaining action is exactly the actual
Mathlib adjoint graph instantiation plus the final self-adjointness promotion
statement. -/
def concreteAnalyticSpineHardResidualR3AfterFinalInputEliminators : Prop :=
  (∀ (G : ConcreteL2R2PairSpace → Prop)
      (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G),
    concreteAnalyticSpineHardResidualR3ActualGraphFinalEliminatorPackage G hG) ∧
  concreteAnalyticSpineHardResidualR3AfterActualGraphProjectionBundle

/-- The post-final-input-eliminator surface is ready. -/
theorem concrete_analytic_spine_hard_residual_r3_after_final_input_eliminators_ready :
    concreteAnalyticSpineHardResidualR3AfterFinalInputEliminators := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_actual_graph_final_eliminator_package_ready,
    concrete_analytic_spine_hard_residual_r3_after_actual_graph_projection_bundle_ready⟩

end

end MathlibAnalytic
end MGAP4D
