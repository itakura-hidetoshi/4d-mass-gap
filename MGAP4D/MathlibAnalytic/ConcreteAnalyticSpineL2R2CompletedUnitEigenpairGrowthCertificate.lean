import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CompletedUnitVectorGrowthCertificate

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Obstruction-selected completed diagonal weight. -/
def concreteL2R2CompletedObstructionEigenvalue (k : ℕ) : ℝ :=
  concreteL2DiagonalWeight
    (concreteL2DiagonalUnboundednessObstructionSurface.witness k)

/-- The completed obstruction output probe is the selected eigenvalue times the
completed obstruction input probe. -/
theorem concrete_l2_r2_completed_obstruction_output_eq_eigenvalue_smul_input
    (k : ℕ) :
    concreteL2R2CompletedObstructionUnitOutputProbe k =
      concreteL2R2CompletedObstructionEigenvalue k •
        concreteL2R2CompletedObstructionUnitInputProbe k := by
  rfl

/-- The obstruction-selected eigenvalue exceeds the requested threshold. -/
theorem concrete_l2_r2_completed_obstruction_eigenvalue_gt_threshold
    (k : ℕ) :
    (k : ℝ) < concreteL2R2CompletedObstructionEigenvalue k := by
  exact concrete_l2_diagonal_obstruction_index_threshold_law k

/-- Completed unit eigenpair growth certificate.

For every threshold `k`, there are completed `l2` vectors `x` and `y` and a real
scalar `lam` such that `‖x‖ = 1`, `y = lam • x`, `k < lam`, and `k < ‖y‖`.
This is still a unit-eigenpair growth certificate, not yet a globally defined
completed operator-norm theorem. -/
def concreteL2R2CompletedUnitEigenpairGrowthCertificate : Prop :=
  ∀ k : ℕ,
    ∃ x y : lp (fun _ : ℕ => ℝ) 2,
      ∃ lam : ℝ,
        x = concreteL2R2CompletedObstructionUnitInputProbe k ∧
        y = concreteL2R2CompletedObstructionUnitOutputProbe k ∧
        lam = concreteL2R2CompletedObstructionEigenvalue k ∧
        ‖x‖ = 1 ∧
        y = lam • x ∧
        (k : ℝ) < lam ∧
        (k : ℝ) < ‖y‖

/-- The completed unit eigenpair growth certificate is ready. -/
theorem concrete_l2_r2_completed_unit_eigenpair_growth_certificate :
    concreteL2R2CompletedUnitEigenpairGrowthCertificate := by
  intro k
  refine ⟨
    concreteL2R2CompletedObstructionUnitInputProbe k,
    concreteL2R2CompletedObstructionUnitOutputProbe k,
    concreteL2R2CompletedObstructionEigenvalue k,
    ?_⟩
  exact ⟨
    rfl,
    rfl,
    rfl,
    concrete_l2_r2_completed_obstruction_unit_input_norm_eq_one k,
    (concrete_l2_r2_completed_obstruction_output_eq_eigenvalue_smul_input k).symm,
    concrete_l2_r2_completed_obstruction_eigenvalue_gt_threshold k,
    concrete_l2_r2_completed_obstruction_unit_output_norm_gt_threshold k⟩

/-- Public theorem-entry predicate for the completed unit-eigenpair growth layer. -/
def concreteAnalyticSpineL2R2CompletedUnitEigenpairGrowthCertificateReady : Prop :=
  concreteAnalyticSpineL2R2CompletedUnitVectorGrowthCertificateReady ∧
  concreteL2R2CompletedUnitEigenpairGrowthCertificate

/-- The completed unit-eigenpair growth certificate layer is ready. -/
theorem concrete_analytic_spine_l2_r2_completed_unit_eigenpair_growth_certificate_ready :
    concreteAnalyticSpineL2R2CompletedUnitEigenpairGrowthCertificateReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_completed_unit_vector_growth_certificate_ready,
    concrete_l2_r2_completed_unit_eigenpair_growth_certificate⟩

end

end MathlibAnalytic
end MGAP4D
