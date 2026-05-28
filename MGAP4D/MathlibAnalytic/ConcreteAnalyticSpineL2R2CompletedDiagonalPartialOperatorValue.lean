import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CompletedDiagonalSingleValuedness

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Subtype domain for the graph-defined completed diagonal operator. -/
abbrev ConcreteL2R2CompletedDiagonalOperatorDomain : Type :=
  {x : lp (fun _ : ℕ => ℝ) 2 //
    x ∈ concreteL2R2CompletedDiagonalOperatorDomainCarrier}

/-- The value of the graph-defined completed diagonal operator at a domain point,
chosen from the graph.  Single-valuedness proves below that this choice is
independent of the witness. -/
def concreteL2R2CompletedDiagonalOperatorValue
    (x : ConcreteL2R2CompletedDiagonalOperatorDomain) :
    lp (fun _ : ℕ => ℝ) 2 :=
  Classical.choose (concrete_l2_r2_completed_diagonal_operator_output_exists x.property)

/-- The chosen value lies in the completed diagonal graph. -/
theorem concrete_l2_r2_completed_diagonal_operator_value_graph_mem
    (x : ConcreteL2R2CompletedDiagonalOperatorDomain) :
    ((x : lp (fun _ : ℕ => ℝ) 2),
      concreteL2R2CompletedDiagonalOperatorValue x) ∈
        concreteL2R2CompletedDiagonalGraphCarrier := by
  exact Classical.choose_spec
    (concrete_l2_r2_completed_diagonal_operator_output_exists x.property)

/-- Any graph output for a domain point is equal to the chosen operator value. -/
theorem concrete_l2_r2_completed_diagonal_operator_value_eq_of_graph
    (x : ConcreteL2R2CompletedDiagonalOperatorDomain)
    {y : lp (fun _ : ℕ => ℝ) 2}
    (hy : ((x : lp (fun _ : ℕ => ℝ) 2), y) ∈
      concreteL2R2CompletedDiagonalGraphCarrier) :
    concreteL2R2CompletedDiagonalOperatorValue x = y := by
  exact concrete_l2_r2_completed_diagonal_graph_single_valued
    (concrete_l2_r2_completed_diagonal_operator_value_graph_mem x) hy

/-- Obstruction-selected domain point for the completed diagonal partial
operator. -/
def concreteL2R2CompletedObstructionDomainPoint (k : ℕ) :
    ConcreteL2R2CompletedDiagonalOperatorDomain :=
  ⟨concreteL2R2CompletedObstructionUnitInputProbe k,
    concrete_l2_r2_completed_obstruction_input_mem_operator_domain k⟩

/-- The chosen value at the obstruction domain point is the obstruction output
probe. -/
theorem concrete_l2_r2_completed_obstruction_operator_value_eq_output
    (k : ℕ) :
    concreteL2R2CompletedDiagonalOperatorValue
        (concreteL2R2CompletedObstructionDomainPoint k) =
      concreteL2R2CompletedObstructionUnitOutputProbe k := by
  exact concrete_l2_r2_completed_diagonal_operator_value_eq_of_graph
    (concreteL2R2CompletedObstructionDomainPoint k)
    (concrete_l2_r2_completed_obstruction_pair_mem_diagonal_graph k)

/-- The partial operator value has unit-domain inputs with arbitrarily large
output norm. -/
def concreteL2R2CompletedDiagonalPartialOperatorValueGrowthCertificate : Prop :=
  ∀ k : ℕ,
    ∃ x : ConcreteL2R2CompletedDiagonalOperatorDomain,
      ‖(x : lp (fun _ : ℕ => ℝ) 2)‖ = 1 ∧
      (k : ℝ) < ‖concreteL2R2CompletedDiagonalOperatorValue x‖

/-- Growth certificate for the chosen partial-operator value. -/
theorem concrete_l2_r2_completed_diagonal_partial_operator_value_growth_certificate :
    concreteL2R2CompletedDiagonalPartialOperatorValueGrowthCertificate := by
  intro k
  refine ⟨concreteL2R2CompletedObstructionDomainPoint k, ?_⟩
  constructor
  · exact concrete_l2_r2_completed_obstruction_unit_input_norm_eq_one k
  · rw [concrete_l2_r2_completed_obstruction_operator_value_eq_output k]
    exact concrete_l2_r2_completed_obstruction_unit_output_norm_gt_threshold k

/-- Public theorem-entry predicate for the completed diagonal partial-operator
value layer. -/
def concreteAnalyticSpineL2R2CompletedDiagonalPartialOperatorValueReady : Prop :=
  concreteAnalyticSpineL2R2CompletedDiagonalSingleValuednessReady ∧
  concreteL2R2CompletedDiagonalPartialOperatorValueGrowthCertificate

/-- The completed diagonal partial-operator value surface is ready. -/
theorem concrete_analytic_spine_l2_r2_completed_diagonal_partial_operator_value_ready :
    concreteAnalyticSpineL2R2CompletedDiagonalPartialOperatorValueReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_completed_diagonal_single_valuedness_ready,
    concrete_l2_r2_completed_diagonal_partial_operator_value_growth_certificate⟩

end

end MathlibAnalytic
end MGAP4D
