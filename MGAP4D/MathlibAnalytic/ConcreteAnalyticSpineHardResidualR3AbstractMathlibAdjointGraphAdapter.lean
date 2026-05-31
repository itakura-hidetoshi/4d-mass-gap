import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3MathlibAdjointIdentificationObligation

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Abstract adapter for the future Mathlib-side adjoint graph predicate.

`G` is the graph predicate that the next implementation should replace by the
actual Mathlib adjoint graph of the completed diagonal operator.  At this stage
we only require that `G` be identified with the already proved concrete formal
adjoint linear-map graph. -/
def concreteAnalyticSpineHardResidualR3AbstractMathlibAdjointGraphIdentification
    (G : ConcreteL2R2PairSpace → Prop) : Prop :=
  G = concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph

/-- If the abstract Mathlib graph is identified with the formal adjoint
linear-map graph, then it is identified with the formal adjoint graph candidate. -/
theorem concrete_analytic_spine_hard_residual_r3_abstract_mathlib_graph_eq_candidate
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3AbstractMathlibAdjointGraphIdentification G) :
    G = concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate := by
  unfold concreteAnalyticSpineHardResidualR3AbstractMathlibAdjointGraphIdentification at hG
  rw [hG]
  exact concrete_analytic_spine_hard_residual_r3_linear_map_graph_eq_formal_adjoint_candidate

/-- If the abstract Mathlib graph is identified with the formal adjoint
linear-map graph, then it is identified with the completed diagonal graph
carrier. -/
theorem concrete_analytic_spine_hard_residual_r3_abstract_mathlib_graph_eq_completed_graph
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3AbstractMathlibAdjointGraphIdentification G) :
    G = concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier := by
  unfold concreteAnalyticSpineHardResidualR3AbstractMathlibAdjointGraphIdentification at hG
  rw [hG]
  exact concrete_analytic_spine_hard_residual_r3_linear_map_graph_eq_completed_diagonal_graph

/-- Abstract Mathlib adjoint graph adapter input.

This turns the remaining Mathlib-side graph-identification theorem into a single
parameter `G`.  Once `G` is supplied as the actual Mathlib adjoint graph and the
identification proof is supplied, the concrete graph equalities are available
without re-opening their proofs. -/
def concreteAnalyticSpineHardResidualR3AbstractMathlibAdjointGraphAdapterInput
    (G : ConcreteL2R2PairSpace → Prop) : Prop :=
  concreteAnalyticSpineHardResidualR3MathlibAdjointGraphIdentificationTarget ∧
  concreteAnalyticSpineHardResidualR3AbstractMathlibAdjointGraphIdentification G ∧
  (G = concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate) ∧
  (G = concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier) ∧
  concreteL2R4FormalGraphSelfAdjointness

/-- The abstract Mathlib adjoint graph adapter input is ready from one graph
identification proof. -/
theorem concrete_analytic_spine_hard_residual_r3_abstract_mathlib_adjoint_graph_adapter_input_ready
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3AbstractMathlibAdjointGraphIdentification G) :
    concreteAnalyticSpineHardResidualR3AbstractMathlibAdjointGraphAdapterInput G := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_mathlib_adjoint_graph_identification_target_ready,
    hG,
    concrete_analytic_spine_hard_residual_r3_abstract_mathlib_graph_eq_candidate G hG,
    concrete_analytic_spine_hard_residual_r3_abstract_mathlib_graph_eq_completed_graph G hG,
    concrete_l2_r4_formal_graph_self_adjointness⟩

/-- The conditional pre-promotion target after a concrete Mathlib adjoint graph
predicate has been supplied and identified.

This still does not assert self-adjointness.  It only says that, conditional on
the graph identification, the future promotion theorem receives the exact graph
and formal self-adjointness inputs it needs. -/
def concreteAnalyticSpineHardResidualR3ConditionalSelfAdjointPrePromotion
    (G : ConcreteL2R2PairSpace → Prop) : Prop :=
  concreteAnalyticSpineHardResidualR3AbstractMathlibAdjointGraphAdapterInput G ∧
  concreteAnalyticSpineHardResidualR3SelfAdjointPromotionSingleTarget ∧
  concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness

/-- Conditional pre-promotion is ready once the abstract Mathlib graph has been
identified with the concrete formal adjoint linear-map graph. -/
theorem concrete_analytic_spine_hard_residual_r3_conditional_self_adjoint_prepromotion_ready
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3AbstractMathlibAdjointGraphIdentification G) :
    concreteAnalyticSpineHardResidualR3ConditionalSelfAdjointPrePromotion G := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_abstract_mathlib_adjoint_graph_adapter_input_ready G hG,
    concrete_analytic_spine_hard_residual_r3_self_adjoint_promotion_single_target_ready,
    concrete_l2_r2_closed_operator_boundary_not_self_adjointness⟩

/-- R3 after the abstract adapter: the remaining concrete task is to instantiate
`G` with the actual Mathlib adjoint graph and prove the identification. -/
def concreteAnalyticSpineHardResidualR3PostAbstractAdapterBlocker : Prop :=
  (∀ G : ConcreteL2R2PairSpace → Prop,
    concreteAnalyticSpineHardResidualR3AbstractMathlibAdjointGraphIdentification G →
      concreteAnalyticSpineHardResidualR3ConditionalSelfAdjointPrePromotion G) ∧
  concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness ∧
  concreteL2R2ClosedOperatorBoundaryNotSpectralTheorem ∧
  concreteL2R2ClosedOperatorBoundaryNotPVM ∧
  concreteL2R2ClosedOperatorBoundaryNotPositiveSpectralWeight

/-- The post-abstract-adapter blocker is visible. -/
theorem concrete_analytic_spine_hard_residual_r3_post_abstract_adapter_blocker_visible :
    concreteAnalyticSpineHardResidualR3PostAbstractAdapterBlocker := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_conditional_self_adjoint_prepromotion_ready,
    concrete_l2_r2_closed_operator_boundary_not_self_adjointness,
    concrete_l2_r2_closed_operator_boundary_not_spectral_theorem,
    concrete_l2_r2_closed_operator_boundary_not_pvm,
    concrete_l2_r2_closed_operator_boundary_not_positive_spectral_weight⟩

end

end MathlibAnalytic
end MGAP4D
