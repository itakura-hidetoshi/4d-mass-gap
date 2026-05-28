import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CompletedUnitProbeOutputNormLowerBound

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Completed `l2` input probe for the obstruction-selected coordinate. -/
def concreteL2R2CompletedObstructionUnitInputProbe (k : ℕ) :
    lp (fun _ : ℕ => ℝ) 2 :=
  concreteL2MathlibUnit
    (concreteL2DiagonalUnboundednessObstructionSurface.witness k)

/-- The completed obstruction input probe has norm one. -/
theorem concrete_l2_r2_completed_obstruction_unit_input_norm_eq_one
    (k : ℕ) :
    ‖concreteL2R2CompletedObstructionUnitInputProbe k‖ = 1 := by
  exact concrete_l2_mathlib_unit_norm_eq_one
    (concreteL2DiagonalUnboundednessObstructionSurface.witness k)

/-- Completed unit-vector growth certificate.

For every threshold `k`, there is a completed `l2` unit vector `x` such that the
corresponding obstruction output probe has norm larger than `k`.  This is still
a paired input/output certificate, not yet a theorem about a globally defined
closed or self-adjoint operator. -/
def concreteL2R2CompletedUnitVectorGrowthCertificate : Prop :=
  ∀ k : ℕ,
    ∃ x : lp (fun _ : ℕ => ℝ) 2,
      x = concreteL2R2CompletedObstructionUnitInputProbe k ∧
      ‖x‖ = 1 ∧
      (k : ℝ) < ‖concreteL2R2CompletedObstructionUnitOutputProbe k‖

/-- The completed unit-vector growth certificate is proved by the obstruction
input probe and the completed output-norm lower bound. -/
theorem concrete_l2_r2_completed_unit_vector_growth_certificate :
    concreteL2R2CompletedUnitVectorGrowthCertificate := by
  intro k
  refine ⟨concreteL2R2CompletedObstructionUnitInputProbe k, ?_⟩
  exact ⟨
    rfl,
    concrete_l2_r2_completed_obstruction_unit_input_norm_eq_one k,
    concrete_l2_r2_completed_obstruction_unit_output_norm_gt_threshold k⟩

/-- Public theorem-entry predicate for the completed unit-vector growth layer. -/
def concreteAnalyticSpineL2R2CompletedUnitVectorGrowthCertificateReady : Prop :=
  concreteAnalyticSpineL2R2CompletedUnitProbeOutputNormLowerBoundReady ∧
  concreteL2R2CompletedUnitVectorGrowthCertificate

/-- The completed unit-vector growth certificate layer is ready. -/
theorem concrete_analytic_spine_l2_r2_completed_unit_vector_growth_certificate_ready :
    concreteAnalyticSpineL2R2CompletedUnitVectorGrowthCertificateReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_completed_unit_probe_output_norm_lower_bound_ready,
    concrete_l2_r2_completed_unit_vector_growth_certificate⟩

end

end MathlibAnalytic
end MGAP4D
