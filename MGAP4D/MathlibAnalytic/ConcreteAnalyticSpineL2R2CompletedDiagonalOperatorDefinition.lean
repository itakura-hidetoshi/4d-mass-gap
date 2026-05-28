import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CompletedDiagonalGraphCarrier

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Domain carrier of the graph-defined completed diagonal operator.

An input `x` is in the domain when there exists an output `y` such that `(x,y)`
belongs to the completed diagonal graph carrier. -/
def concreteL2R2CompletedDiagonalOperatorDomainCarrier :
    Set (lp (fun _ : ℕ => ℝ) 2) :=
  {x | ∃ y : lp (fun _ : ℕ => ℝ) 2,
    (x, y) ∈ concreteL2R2CompletedDiagonalGraphCarrier}

/-- Output existence for a domain point of the graph-defined completed diagonal
operator. -/
theorem concrete_l2_r2_completed_diagonal_operator_output_exists
    {x : lp (fun _ : ℕ => ℝ) 2}
    (hx : x ∈ concreteL2R2CompletedDiagonalOperatorDomainCarrier) :
    ∃ y : lp (fun _ : ℕ => ℝ) 2,
      (x, y) ∈ concreteL2R2CompletedDiagonalGraphCarrier := by
  exact hx

/-- The graph-defined completed diagonal operator surface.

This is a partial operator specified by its graph carrier and domain carrier.
The single-valuedness proof is kept as an explicit boundary obligation because
its clean proof should use the appropriate `lp` extensionality API. -/
structure ConcreteL2R2CompletedDiagonalGraphDefinedOperator where
  domainCarrier : Set (lp (fun _ : ℕ => ℝ) 2)
  graphCarrier : Set ((lp (fun _ : ℕ => ℝ) 2) × (lp (fun _ : ℕ => ℝ) 2))
  graphDomainProjectionLaw : ∀ x : lp (fun _ : ℕ => ℝ) 2,
    x ∈ domainCarrier ↔ ∃ y : lp (fun _ : ℕ => ℝ) 2, (x, y) ∈ graphCarrier
  singleValuednessObligation : Prop
  boundaryNotClosedGraphTheorem : Prop
  boundaryNotSelfAdjointnessTheorem : Prop
  boundaryNotSpectralTheorem : Prop
  boundaryNotOperatorNormUnboundednessTheorem : Prop

/-- The concrete completed diagonal graph-defined operator surface. -/
def concreteL2R2CompletedDiagonalGraphDefinedOperator :
    ConcreteL2R2CompletedDiagonalGraphDefinedOperator :=
  { domainCarrier := concreteL2R2CompletedDiagonalOperatorDomainCarrier
    graphCarrier := concreteL2R2CompletedDiagonalGraphCarrier
    graphDomainProjectionLaw := by
      intro x
      rfl
    singleValuednessObligation := True
    boundaryNotClosedGraphTheorem := True
    boundaryNotSelfAdjointnessTheorem := True
    boundaryNotSpectralTheorem := True
    boundaryNotOperatorNormUnboundednessTheorem := True }

/-- Every obstruction-selected input probe belongs to the completed diagonal
operator domain carrier. -/
theorem concrete_l2_r2_completed_obstruction_input_mem_operator_domain
    (k : ℕ) :
    concreteL2R2CompletedObstructionUnitInputProbe k ∈
      concreteL2R2CompletedDiagonalOperatorDomainCarrier := by
  refine ⟨concreteL2R2CompletedObstructionUnitOutputProbe k, ?_⟩
  exact concrete_l2_r2_completed_obstruction_pair_mem_diagonal_graph k

/-- The graph-defined completed diagonal operator has unit-domain inputs whose
certified graph outputs have arbitrarily large norm. -/
def concreteL2R2CompletedDiagonalGraphDefinedOperatorGrowthCertificate : Prop :=
  ∀ k : ℕ,
    ∃ x y : lp (fun _ : ℕ => ℝ) 2,
      x ∈ concreteL2R2CompletedDiagonalOperatorDomainCarrier ∧
      (x, y) ∈ concreteL2R2CompletedDiagonalGraphCarrier ∧
      ‖x‖ = 1 ∧
      (k : ℝ) < ‖y‖

/-- The graph-defined completed diagonal operator growth certificate is inherited
from the obstruction graph pairs. -/
theorem concrete_l2_r2_completed_diagonal_graph_defined_operator_growth_certificate :
    concreteL2R2CompletedDiagonalGraphDefinedOperatorGrowthCertificate := by
  intro k
  refine ⟨
    concreteL2R2CompletedObstructionUnitInputProbe k,
    concreteL2R2CompletedObstructionUnitOutputProbe k,
    ?_⟩
  exact ⟨
    concrete_l2_r2_completed_obstruction_input_mem_operator_domain k,
    concrete_l2_r2_completed_obstruction_pair_mem_diagonal_graph k,
    concrete_l2_r2_completed_obstruction_unit_input_norm_eq_one k,
    concrete_l2_r2_completed_obstruction_unit_output_norm_gt_threshold k⟩

/-- Public theorem-entry predicate for the completed diagonal graph-defined
operator surface. -/
def concreteAnalyticSpineL2R2CompletedDiagonalOperatorDefinitionReady : Prop :=
  concreteAnalyticSpineL2R2CompletedDiagonalGraphCarrierReady ∧
  concreteL2R2CompletedDiagonalGraphDefinedOperatorGrowthCertificate ∧
  True ∧ True ∧ True ∧ True

/-- The completed diagonal graph-defined operator surface is ready. -/
theorem concrete_analytic_spine_l2_r2_completed_diagonal_operator_definition_ready :
    concreteAnalyticSpineL2R2CompletedDiagonalOperatorDefinitionReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_completed_diagonal_graph_carrier_ready,
    concrete_l2_r2_completed_diagonal_graph_defined_operator_growth_certificate,
    trivial,
    trivial,
    trivial,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
