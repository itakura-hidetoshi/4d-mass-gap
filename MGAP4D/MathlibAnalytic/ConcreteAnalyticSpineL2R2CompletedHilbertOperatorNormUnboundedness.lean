import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CompletedDiagonalOperatorClosedness

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Operator-norm unboundedness for the graph-defined completed diagonal operator.

There is no natural-number bound `K` that uniformly bounds the graph output norm
on unit-norm domain inputs.  This is the graph-defined operator-norm obstruction
needed before any self-adjoint/spectral promotion can be considered. -/
def concreteL2R2CompletedHilbertOperatorNormUnboundedness : Prop :=
  ¬ ∃ K : ℕ,
    ∀ x y : lp (fun _ : ℕ => ℝ) 2,
      x ∈ concreteL2R2CompletedDiagonalOperatorDomainCarrier →
      (x, y) ∈ concreteL2R2CompletedDiagonalGraphDefinedOperator.graphCarrier →
      ‖x‖ = 1 →
      ‖y‖ ≤ (K : ℝ)

/-- The graph-defined completed diagonal operator is unbounded on unit-domain
inputs. -/
theorem concrete_l2_r2_completed_hilbert_operator_norm_unboundedness :
    concreteL2R2CompletedHilbertOperatorNormUnboundedness := by
  rintro ⟨K, hK⟩
  obtain ⟨x, y, hxdom, hgraph, hxnorm, hgt⟩ :=
    concrete_l2_r2_completed_diagonal_graph_defined_operator_growth_certificate (K + 1)
  have hle : ‖y‖ ≤ (K : ℝ) := by
    exact hK x y hxdom hgraph hxnorm
  have hKlt : (K : ℝ) < ((K + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_succ_self K
  exact (not_lt_of_ge hle) (lt_trans hKlt hgt)

/-- Public theorem-entry predicate for the completed Hilbert operator-norm
unboundedness layer. -/
def concreteAnalyticSpineL2R2CompletedHilbertOperatorNormUnboundednessReady : Prop :=
  concreteAnalyticSpineL2R2CompletedDiagonalOperatorClosednessReady ∧
  concreteL2R2CompletedHilbertOperatorNormUnboundedness

/-- The completed Hilbert operator-norm unboundedness layer is ready. -/
theorem concrete_analytic_spine_l2_r2_completed_hilbert_operator_norm_unboundedness_ready :
    concreteAnalyticSpineL2R2CompletedHilbertOperatorNormUnboundednessReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_completed_diagonal_operator_closedness_ready,
    concrete_l2_r2_completed_hilbert_operator_norm_unboundedness⟩

end

end MathlibAnalytic
end MGAP4D
