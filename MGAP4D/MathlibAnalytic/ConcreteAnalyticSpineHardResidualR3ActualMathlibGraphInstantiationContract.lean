import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3CanonicalFormalActualGraphSpecialization

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Actual Mathlib graph instantiation contract.

To instantiate the genuine Mathlib adjoint graph, it is enough to provide a
predicate `G` and a proof that `G` identifies with the canonical formal graph.
This contract then packages all already-proved R3 graph-transport and theorem
pre-input surfaces for that `G`. -/
def concreteAnalyticSpineHardResidualR3ActualMathlibGraphInstantiationContract
    (G : ConcreteL2R2PairSpace → Prop) : Prop :=
  ∃ hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G,
    concreteAnalyticSpineHardResidualR3ActualGraphSelfAdjointTheoremPreInputClosed G hG ∧
    concreteAnalyticSpineHardResidualR3ActualGraphFormalSelfAdjointTransport G hG ∧
    (∀ p : ConcreteL2R2PairSpace,
      G p ↔ concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph p) ∧
    (∀ p : ConcreteL2R2PairSpace,
      G p ↔ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p) ∧
    (∀ p : ConcreteL2R2PairSpace,
      G p ↔ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p) ∧
    concreteL2R4FormalGraphSelfAdjointness ∧
    concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness

/-- Any graph predicate equipped with a canonical-formal equality proof satisfies
the actual Mathlib graph instantiation contract. -/
theorem concrete_analytic_spine_hard_residual_r3_actual_mathlib_graph_instantiation_contract_from_identification
    (G : ConcreteL2R2PairSpace → Prop)
    (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G) :
    concreteAnalyticSpineHardResidualR3ActualMathlibGraphInstantiationContract G := by
  let hclosed :=
    concrete_analytic_spine_hard_residual_r3_actual_graph_self_adjoint_theorem_preinput_closed_ready G hG
  let htransport :=
    concrete_analytic_spine_hard_residual_r3_actual_graph_formal_self_adjoint_transport_ready G hG
  exact ⟨hG,
    hclosed,
    htransport,
    concrete_analytic_spine_hard_residual_r3_actual_formal_transport_iff_linear_map G hG htransport,
    concrete_analytic_spine_hard_residual_r3_actual_formal_transport_iff_candidate G hG htransport,
    concrete_analytic_spine_hard_residual_r3_actual_formal_transport_iff_completed_graph G hG htransport,
    concrete_analytic_spine_hard_residual_r3_actual_formal_transport_formal_self_adjointness G hG htransport,
    concrete_analytic_spine_hard_residual_r3_actual_formal_transport_boundary_not_self_adjointness G hG htransport⟩

/-- The canonical formal graph predicate satisfies the actual Mathlib graph
instantiation contract by reflexivity. -/
theorem concrete_analytic_spine_hard_residual_r3_canonical_formal_graph_instantiation_contract_ready :
    concreteAnalyticSpineHardResidualR3ActualMathlibGraphInstantiationContract
      concreteAnalyticSpineHardResidualR3CanonicalFormalGraphPredicate := by
  exact concrete_analytic_spine_hard_residual_r3_actual_mathlib_graph_instantiation_contract_from_identification
    concreteAnalyticSpineHardResidualR3CanonicalFormalGraphPredicate
    concrete_analytic_spine_hard_residual_r3_canonical_formal_graph_identifies_canonical_formal

/-- Elimination: an instantiation contract exposes its canonical-formal equality proof. -/
theorem concrete_analytic_spine_hard_residual_r3_instantiation_contract_identification
    (G : ConcreteL2R2PairSpace → Prop)
    (h : concreteAnalyticSpineHardResidualR3ActualMathlibGraphInstantiationContract G) :
    ∃ hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G,
      True := by
  rcases h with ⟨hG, _⟩
  exact ⟨hG, True.intro⟩

/-- Elimination: an instantiation contract exposes a closed theorem pre-input for
its chosen canonical-formal equality witness. -/
theorem concrete_analytic_spine_hard_residual_r3_instantiation_contract_closed_preinput
    (G : ConcreteL2R2PairSpace → Prop)
    (h : concreteAnalyticSpineHardResidualR3ActualMathlibGraphInstantiationContract G) :
    ∃ hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G,
      concreteAnalyticSpineHardResidualR3ActualGraphSelfAdjointTheoremPreInputClosed G hG := by
  rcases h with ⟨hG, hclosed, _⟩
  exact ⟨hG, hclosed⟩

/-- Elimination: an instantiation contract exposes the actual graph pointwise
iff with the completed graph carrier. -/
theorem concrete_analytic_spine_hard_residual_r3_instantiation_contract_iff_completed_graph
    (G : ConcreteL2R2PairSpace → Prop)
    (h : concreteAnalyticSpineHardResidualR3ActualMathlibGraphInstantiationContract G) :
    ∀ p : ConcreteL2R2PairSpace,
      G p ↔ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p := by
  rcases h with ⟨_, _, _, _, _, hcompleted, _, _⟩
  exact hcompleted

/-- Elimination: an instantiation contract exposes the actual graph pointwise
iff with the formal adjoint candidate graph. -/
theorem concrete_analytic_spine_hard_residual_r3_instantiation_contract_iff_candidate
    (G : ConcreteL2R2PairSpace → Prop)
    (h : concreteAnalyticSpineHardResidualR3ActualMathlibGraphInstantiationContract G) :
    ∀ p : ConcreteL2R2PairSpace,
      G p ↔ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p := by
  rcases h with ⟨_, _, _, _, hcandidate, _, _, _⟩
  exact hcandidate

/-- R3 after the actual Mathlib graph instantiation contract.

The formal graph path is closed for any `G` with a canonical-formal equality
proof, and the canonical formal graph itself is already instantiated.  The only
remaining mathematical step is to choose the genuine Mathlib adjoint graph
predicate and prove that equality. -/
def concreteAnalyticSpineHardResidualR3AfterActualMathlibGraphInstantiationContract : Prop :=
  (∀ (G : ConcreteL2R2PairSpace → Prop)
      (hG : concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal G),
    concreteAnalyticSpineHardResidualR3ActualMathlibGraphInstantiationContract G) ∧
  concreteAnalyticSpineHardResidualR3ActualMathlibGraphInstantiationContract
    concreteAnalyticSpineHardResidualR3CanonicalFormalGraphPredicate ∧
  concreteAnalyticSpineHardResidualR3AfterCanonicalFormalActualGraphSpecialization

/-- The post-actual-Mathlib-graph-instantiation-contract surface is ready. -/
theorem concrete_analytic_spine_hard_residual_r3_after_actual_mathlib_graph_instantiation_contract_ready :
    concreteAnalyticSpineHardResidualR3AfterActualMathlibGraphInstantiationContract := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_actual_mathlib_graph_instantiation_contract_from_identification,
    concrete_analytic_spine_hard_residual_r3_canonical_formal_graph_instantiation_contract_ready,
    concrete_analytic_spine_hard_residual_r3_after_canonical_formal_actual_graph_specialization_ready⟩

end

end MathlibAnalytic
end MGAP4D
