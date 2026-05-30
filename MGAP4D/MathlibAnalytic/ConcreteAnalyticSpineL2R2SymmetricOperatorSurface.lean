import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2InnerProductIdentification
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2SelfAdjointnessConcretePreconditions

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Symmetry predicate for the completed diagonal graph-defined operator.

This is the operator-theoretic symmetry condition in graph form: whenever
`(x, Tx)` and `(z, Tz)` are graph points, the real Hilbert inner product satisfies
`⟪Tx, z⟫ = ⟪x, Tz⟫`.  It is intentionally stated on the graph carrier rather than
on a total function, because the completed diagonal lane is presently a
partial graph-defined operator. -/
def concreteL2R2CompletedDiagonalGraphSymmetric : Prop :=
  ∀ {x Tx z Tz : lp (fun _ : ℕ => ℝ) 2},
    (x, Tx) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
    (z, Tz) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
    inner ℝ Tx z = inner ℝ x Tz

/-- The completed diagonal graph-defined operator is symmetric in the real Hilbert
inner product sense. -/
theorem concrete_l2_r2_completed_diagonal_graph_symmetric :
    concreteL2R2CompletedDiagonalGraphSymmetric := by
  intro x Tx z Tz hxgraph hzgraph
  exact concrete_l2_r2_inner_product_graph_symmetry hxgraph hzgraph

/-- A concrete symmetric-operator surface for the completed diagonal graph-defined
operator.

The surface records the already established concrete self-adjointness
preconditions and upgrades the previous boundary placeholder for symmetry into an
actual theorem.  It still does not assert adjoint-domain agreement,
resolvent/deficiency control, essential self-adjointness, self-adjointness,
spectral theorem, PVM, or positive spectral weight. -/
structure ConcreteL2R2SymmetricOperatorSurface where
  selfAdjointnessConcretePreconditionsReady :
    concreteAnalyticSpineL2R2SelfAdjointnessConcretePreconditionsReady
  innerProductIdentificationReady :
    concreteAnalyticSpineL2R2InnerProductIdentificationReady
  graphSymmetric : concreteL2R2CompletedDiagonalGraphSymmetric
  boundaryNotAdjointDomainAgreementTheorem : Prop
  boundaryNotResolventOrDeficiencyTheorem : Prop
  boundaryNotEssentialSelfAdjointnessTheorem : Prop
  boundaryNotSelfAdjointnessTheorem : Prop
  boundaryNotSpectralTheorem : Prop
  boundaryNotPVM : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete symmetric-operator surface for the completed diagonal lane. -/
def concreteL2R2SymmetricOperatorSurface :
    ConcreteL2R2SymmetricOperatorSurface :=
  { selfAdjointnessConcretePreconditionsReady :=
      concrete_analytic_spine_l2_r2_self_adjointness_concrete_preconditions_ready
    innerProductIdentificationReady :=
      concrete_analytic_spine_l2_r2_inner_product_identification_ready
    graphSymmetric :=
      concrete_l2_r2_completed_diagonal_graph_symmetric
    boundaryNotAdjointDomainAgreementTheorem := True
    boundaryNotResolventOrDeficiencyTheorem := True
    boundaryNotEssentialSelfAdjointnessTheorem := True
    boundaryNotSelfAdjointnessTheorem := True
    boundaryNotSpectralTheorem := True
    boundaryNotPVM := True
    boundaryNotPositiveSpectralWeight := True }

/-- Public theorem-entry predicate for the symmetric operator surface. -/
def concreteAnalyticSpineL2R2SymmetricOperatorSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2SelfAdjointnessConcretePreconditionsReady ∧
  concreteAnalyticSpineL2R2InnerProductIdentificationReady ∧
  concreteL2R2CompletedDiagonalGraphSymmetric ∧
  True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True

/-- The symmetric operator surface is ready. -/
theorem concrete_analytic_spine_l2_r2_symmetric_operator_surface_ready :
    concreteAnalyticSpineL2R2SymmetricOperatorSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_self_adjointness_concrete_preconditions_ready,
    concrete_analytic_spine_l2_r2_inner_product_identification_ready,
    concrete_l2_r2_completed_diagonal_graph_symmetric,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
