import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineHardResidualR3ActualGraphSelfAdjointTheoremPreInputEliminators

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The canonical formal graph predicate, viewed as the actual-graph parameter
for the R3 actual-graph pre-input machinery. -/
def concreteAnalyticSpineHardResidualR3CanonicalFormalGraphPredicate :
    ConcreteL2R2PairSpace → Prop :=
  concreteAnalyticSpineHardResidualR3CanonicalFormalAdjointGraphSlot.mathlibAdjointGraph

/-- The canonical formal graph predicate identifies with the canonical formal slot by reflexivity. -/
theorem concrete_analytic_spine_hard_residual_r3_canonical_formal_graph_identifies_canonical_formal :
    concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal
      concreteAnalyticSpineHardResidualR3CanonicalFormalGraphPredicate := by
  unfold concreteAnalyticSpineHardResidualR3ActualMathlibGraphIdentifiesCanonicalFormal
  unfold concreteAnalyticSpineHardResidualR3CanonicalFormalGraphPredicate
  rfl

/-- Closed pre-input package specialized to the canonical formal graph predicate. -/
def concreteAnalyticSpineHardResidualR3CanonicalFormalActualGraphPreInputClosed : Prop :=
  concreteAnalyticSpineHardResidualR3ActualGraphSelfAdjointTheoremPreInputClosed
    concreteAnalyticSpineHardResidualR3CanonicalFormalGraphPredicate
    concrete_analytic_spine_hard_residual_r3_canonical_formal_graph_identifies_canonical_formal

/-- The closed pre-input package is ready for the canonical formal graph predicate. -/
theorem concrete_analytic_spine_hard_residual_r3_canonical_formal_actual_graph_preinput_closed_ready :
    concreteAnalyticSpineHardResidualR3CanonicalFormalActualGraphPreInputClosed := by
  exact concrete_analytic_spine_hard_residual_r3_actual_graph_self_adjoint_theorem_preinput_closed_ready
    concreteAnalyticSpineHardResidualR3CanonicalFormalGraphPredicate
    concrete_analytic_spine_hard_residual_r3_canonical_formal_graph_identifies_canonical_formal

/-- The canonical formal graph predicate is pointwise equivalent to the formal
adjoint linear-map graph. -/
theorem concrete_analytic_spine_hard_residual_r3_canonical_formal_graph_iff_formal_linear_map :
    ∀ p : ConcreteL2R2PairSpace,
      concreteAnalyticSpineHardResidualR3CanonicalFormalGraphPredicate p ↔
        concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph p := by
  let hpre :=
    concrete_analytic_spine_hard_residual_r3_actual_graph_self_adjoint_theorem_preinput_ready
      concreteAnalyticSpineHardResidualR3CanonicalFormalGraphPredicate
      concrete_analytic_spine_hard_residual_r3_canonical_formal_graph_identifies_canonical_formal
  exact concrete_analytic_spine_hard_residual_r3_actual_preinput_iff_linear_map
    concreteAnalyticSpineHardResidualR3CanonicalFormalGraphPredicate
    concrete_analytic_spine_hard_residual_r3_canonical_formal_graph_identifies_canonical_formal
    hpre

/-- The canonical formal graph predicate is pointwise equivalent to the formal
adjoint candidate graph. -/
theorem concrete_analytic_spine_hard_residual_r3_canonical_formal_graph_iff_candidate :
    ∀ p : ConcreteL2R2PairSpace,
      concreteAnalyticSpineHardResidualR3CanonicalFormalGraphPredicate p ↔
        concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p := by
  let hpre :=
    concrete_analytic_spine_hard_residual_r3_actual_graph_self_adjoint_theorem_preinput_ready
      concreteAnalyticSpineHardResidualR3CanonicalFormalGraphPredicate
      concrete_analytic_spine_hard_residual_r3_canonical_formal_graph_identifies_canonical_formal
  exact concrete_analytic_spine_hard_residual_r3_actual_preinput_iff_candidate
    concreteAnalyticSpineHardResidualR3CanonicalFormalGraphPredicate
    concrete_analytic_spine_hard_residual_r3_canonical_formal_graph_identifies_canonical_formal
    hpre

/-- The canonical formal graph predicate is pointwise equivalent to the completed
operator graph carrier. -/
theorem concrete_analytic_spine_hard_residual_r3_canonical_formal_graph_iff_completed_graph :
    ∀ p : ConcreteL2R2PairSpace,
      concreteAnalyticSpineHardResidualR3CanonicalFormalGraphPredicate p ↔
        concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p := by
  let hpre :=
    concrete_analytic_spine_hard_residual_r3_actual_graph_self_adjoint_theorem_preinput_ready
      concreteAnalyticSpineHardResidualR3CanonicalFormalGraphPredicate
      concrete_analytic_spine_hard_residual_r3_canonical_formal_graph_identifies_canonical_formal
  exact concrete_analytic_spine_hard_residual_r3_actual_preinput_iff_completed_graph
    concreteAnalyticSpineHardResidualR3CanonicalFormalGraphPredicate
    concrete_analytic_spine_hard_residual_r3_canonical_formal_graph_identifies_canonical_formal
    hpre

/-- Canonical formal actual-graph specialization package. -/
def concreteAnalyticSpineHardResidualR3CanonicalFormalActualGraphSpecializationPackage : Prop :=
  concreteAnalyticSpineHardResidualR3CanonicalFormalActualGraphPreInputClosed ∧
  (∀ p : ConcreteL2R2PairSpace,
    concreteAnalyticSpineHardResidualR3CanonicalFormalGraphPredicate p ↔
      concreteL2R2CompletedDiagonalFormalAdjointLinearMapGraph p) ∧
  (∀ p : ConcreteL2R2PairSpace,
    concreteAnalyticSpineHardResidualR3CanonicalFormalGraphPredicate p ↔
      concreteL2R2CompletedDiagonalFormalAdjointGraphCandidate p) ∧
  (∀ p : ConcreteL2R2PairSpace,
    concreteAnalyticSpineHardResidualR3CanonicalFormalGraphPredicate p ↔
      concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier p) ∧
  concreteL2R4FormalGraphSelfAdjointness ∧
  concreteL2R2ClosedOperatorBoundaryNotSelfAdjointness

/-- The canonical formal actual-graph specialization package is ready. -/
theorem concrete_analytic_spine_hard_residual_r3_canonical_formal_actual_graph_specialization_package_ready :
    concreteAnalyticSpineHardResidualR3CanonicalFormalActualGraphSpecializationPackage := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_canonical_formal_actual_graph_preinput_closed_ready,
    concrete_analytic_spine_hard_residual_r3_canonical_formal_graph_iff_formal_linear_map,
    concrete_analytic_spine_hard_residual_r3_canonical_formal_graph_iff_candidate,
    concrete_analytic_spine_hard_residual_r3_canonical_formal_graph_iff_completed_graph,
    concrete_l2_r4_formal_graph_self_adjointness,
    concrete_l2_r2_closed_operator_boundary_not_self_adjointness⟩

/-- R3 after specializing the actual-graph machinery to the canonical formal
graph itself.  This removes the variable `G` from the closed formal path; the
remaining non-formal step is still the genuine actual Mathlib graph predicate. -/
def concreteAnalyticSpineHardResidualR3AfterCanonicalFormalActualGraphSpecialization : Prop :=
  concreteAnalyticSpineHardResidualR3CanonicalFormalActualGraphSpecializationPackage ∧
  concreteAnalyticSpineHardResidualR3AfterActualGraphSelfAdjointTheoremPreInputEliminators

/-- The post-canonical-formal actual-graph specialization surface is ready. -/
theorem concrete_analytic_spine_hard_residual_r3_after_canonical_formal_actual_graph_specialization_ready :
    concreteAnalyticSpineHardResidualR3AfterCanonicalFormalActualGraphSpecialization := by
  exact ⟨
    concrete_analytic_spine_hard_residual_r3_canonical_formal_actual_graph_specialization_package_ready,
    concrete_analytic_spine_hard_residual_r3_after_actual_graph_self_adjoint_theorem_preinput_eliminators_ready⟩

end

end MathlibAnalytic
end MGAP4D
