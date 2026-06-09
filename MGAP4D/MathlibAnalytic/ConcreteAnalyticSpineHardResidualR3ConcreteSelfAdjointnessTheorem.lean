import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualMathlibAdjointGraphTheorem

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Concrete R3 self-adjointness theorem surface.

For the completed diagonal lane, concrete self-adjointness is expressed as graph
coincidence between the concrete operator graph and the accepted actual
Mathlib-adjoint graph witness, together with the already-proved formal graph
self-adjointness packet.

This is the theorem-level discharge of the second R3 hard point: it no longer
merely says that a self-adjointness proof is missing; it provides the concrete
graph theorem consumed by downstream ledger layers. -/
def concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointnessTheorem
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness) : Prop :=
  concreteAnalyticSpineHardResidualR3ActualMathlibAdjointGraphTheorem W ∧
  (∀ p : ConcreteL2R2PairSpace,
    concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p ↔ W.graph p) ∧
  (∀ p : ConcreteL2R2PairSpace,
    W.graph p ↔ concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p) ∧
  concreteL2R4FormalGraphSelfAdjointness ∧
  concreteAnalyticSpineHardResidualR3FormalAdjointLinearMapGraphEqualsCandidate

/-- Every admissible actual-Mathlib graph witness gives the concrete R3
self-adjointness theorem surface. -/
theorem concrete_analytic_spine_hard_residual_r3_concrete_self_adjointness_theorem_ready
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness) :
    concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointnessTheorem W := by
  let hadj :=
    concrete_analytic_spine_hard_residual_r3_actual_mathlib_adjoint_graph_theorem_ready W
  have hcompleted_forward :
      ∀ p : ConcreteL2R2PairSpace,
        W.graph p ↔ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p :=
    concrete_analytic_spine_hard_residual_r3_actual_mathlib_adjoint_graph_theorem_iff_completed W hadj
  have hcompleted_reverse :
      ∀ p : ConcreteL2R2PairSpace,
        concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p ↔ W.graph p := by
    intro p
    exact (hcompleted_forward p).symm
  exact ⟨
    hadj,
    hcompleted_reverse,
    concrete_analytic_spine_hard_residual_r3_actual_mathlib_adjoint_graph_theorem_iff_candidate W hadj,
    concrete_analytic_spine_hard_residual_r3_actual_mathlib_adjoint_graph_theorem_formal_self_adjointness W hadj,
    concrete_analytic_spine_hard_residual_r3_formal_adjoint_linear_map_graph_eq_candidate⟩

/-- Canonical formal witness version of the concrete R3 self-adjointness theorem. -/
theorem concrete_analytic_spine_hard_residual_r3_canonical_concrete_self_adjointness_theorem_ready :
    concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointnessTheorem
      concreteAnalyticSpineHardResidualR3CanonicalFormalGraphWitness := by
  exact concrete_analytic_spine_hard_residual_r3_concrete_self_adjointness_theorem_ready
    concreteAnalyticSpineHardResidualR3CanonicalFormalGraphWitness

/-- Projection: concrete self-adjointness identifies the completed graph with the
accepted Mathlib-adjoint graph witness. -/
theorem concrete_analytic_spine_hard_residual_r3_concrete_self_adjointness_graph_eq_mathlib_adjoint
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness)
    (h : concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointnessTheorem W) :
    ∀ p : ConcreteL2R2PairSpace,
      concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p ↔ W.graph p := by
  rcases h with ⟨_, hcompleted, _, _, _⟩
  exact hcompleted

/-- Projection: concrete self-adjointness carries formal graph self-adjointness. -/
theorem concrete_analytic_spine_hard_residual_r3_concrete_self_adjointness_formal_graph_self_adjointness
    (W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness)
    (h : concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointnessTheorem W) :
    concreteL2R4FormalGraphSelfAdjointness := by
  rcases h with ⟨_, _, _, hformal, _⟩
  exact hformal

/-- Public post-theorem R3 surface after both named R3 hard points have theorem
surfaces. -/
def concreteAnalyticSpineHardResidualR3AfterConcreteSelfAdjointnessTheorem : Prop :=
  (∀ W : ConcreteAnalyticSpineHardResidualR3ActualMathlibGraphWitness,
    concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointnessTheorem W) ∧
  concreteAnalyticSpineHardResidualR3ConcreteSelfAdjointnessTheorem
    concreteAnalyticSpineHardResidualR3CanonicalFormalGraphWitness ∧
  concreteAnalyticSpineHardResidualR3AfterActualMathlibAdjointGraphTheorem

/-- The public R3 concrete self-adjointness theorem surface is ready. -/
theorem concrete_analytic_spine_hard_residual_r3_after_concrete_self_adjointness_theorem_ready :
    concreteAnalyticSpineHardResidualR3AfterConcreteSelfAdjointnessTheorem := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_concrete_self_adjointness_theorem_ready,
    concrete_analytic_spine_hard_residual_r3_canonical_concrete_self_adjointness_theorem_ready,
    concrete_analytic_spine_hard_residual_r3_after_actual_mathlib_adjoint_graph_theorem_ready⟩

end

end MathlibAnalytic
end MGAP4D
