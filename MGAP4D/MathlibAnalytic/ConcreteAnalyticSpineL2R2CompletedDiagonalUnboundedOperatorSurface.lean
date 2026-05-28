import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CompletedDiagonalPartialOperatorValue

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Consolidated R2 surface for the completed diagonal unbounded-operator route.

This is the first non-placeholder operator-side package for checklist item 2.  It
bundles the completed diagonal graph carrier, the graph-defined domain, graph
single-valuedness, the chosen partial operator value, and the unit-vector growth
certificate for that value.

It deliberately does not assert closed graph, self-adjointness, spectral theorem,
PVM construction, exact atom `33/20`, or positive spectral weight. -/
structure ConcreteL2R2CompletedDiagonalUnboundedOperatorSurface where
  diagonalGraphCarrierReady : concreteAnalyticSpineL2R2CompletedDiagonalGraphCarrierReady
  diagonalOperatorDefinitionReady : concreteAnalyticSpineL2R2CompletedDiagonalOperatorDefinitionReady
  diagonalSingleValuednessReady : concreteAnalyticSpineL2R2CompletedDiagonalSingleValuednessReady
  partialOperatorValueReady : concreteAnalyticSpineL2R2CompletedDiagonalPartialOperatorValueReady
  graphSingleValuedness : concreteL2R2CompletedDiagonalSingleValuednessTheorem
  partialValueGrowth : concreteL2R2CompletedDiagonalPartialOperatorValueGrowthCertificate
  boundaryNotCompletedClosedGraphTheorem : Prop
  boundaryNotCompletedOperatorNormTheorem : Prop
  boundaryNotSelfAdjointnessTheorem : Prop
  boundaryNotSpectralTheorem : Prop

/-- The consolidated completed diagonal unbounded-operator surface. -/
def concreteL2R2CompletedDiagonalUnboundedOperatorSurface :
    ConcreteL2R2CompletedDiagonalUnboundedOperatorSurface :=
  { diagonalGraphCarrierReady :=
      concrete_analytic_spine_l2_r2_completed_diagonal_graph_carrier_ready
    diagonalOperatorDefinitionReady :=
      concrete_analytic_spine_l2_r2_completed_diagonal_operator_definition_ready
    diagonalSingleValuednessReady :=
      concrete_analytic_spine_l2_r2_completed_diagonal_single_valuedness_ready
    partialOperatorValueReady :=
      concrete_analytic_spine_l2_r2_completed_diagonal_partial_operator_value_ready
    graphSingleValuedness :=
      concrete_l2_r2_completed_diagonal_single_valuedness_theorem
    partialValueGrowth :=
      concrete_l2_r2_completed_diagonal_partial_operator_value_growth_certificate
    boundaryNotCompletedClosedGraphTheorem := True
    boundaryNotCompletedOperatorNormTheorem := True
    boundaryNotSelfAdjointnessTheorem := True
    boundaryNotSpectralTheorem := True }

/-- Main consolidated theorem for the R2 completed diagonal unbounded-operator
surface.

This theorem packages the actual completed `l2` diagonal partial operator with
unit-domain vectors whose chosen operator values have arbitrarily large norm. -/
def concreteL2R2CompletedDiagonalUnboundedOperatorSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2CompletedDiagonalGraphCarrierReady ∧
  concreteAnalyticSpineL2R2CompletedDiagonalOperatorDefinitionReady ∧
  concreteAnalyticSpineL2R2CompletedDiagonalSingleValuednessReady ∧
  concreteAnalyticSpineL2R2CompletedDiagonalPartialOperatorValueReady ∧
  concreteL2R2CompletedDiagonalSingleValuednessTheorem ∧
  concreteL2R2CompletedDiagonalPartialOperatorValueGrowthCertificate ∧
  True ∧ True ∧ True ∧ True

/-- The R2 completed diagonal unbounded-operator surface is ready. -/
theorem concrete_analytic_spine_l2_r2_completed_diagonal_unbounded_operator_surface_ready :
    concreteL2R2CompletedDiagonalUnboundedOperatorSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_completed_diagonal_graph_carrier_ready,
    concrete_analytic_spine_l2_r2_completed_diagonal_operator_definition_ready,
    concrete_analytic_spine_l2_r2_completed_diagonal_single_valuedness_ready,
    concrete_analytic_spine_l2_r2_completed_diagonal_partial_operator_value_ready,
    concrete_l2_r2_completed_diagonal_single_valuedness_theorem,
    concrete_l2_r2_completed_diagonal_partial_operator_value_growth_certificate,
    trivial,
    trivial,
    trivial,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
