import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2UnitProbeActionMassLowerBound
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibNormAdapter

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Mathlib completed-`l2` output probe for the obstruction-selected unit.

This is the completed Hilbert-side vector corresponding to the finite-support
calculation `A e_w = w e_w`, where `w` is the obstruction-selected diagonal
weight. -/
def concreteL2R2CompletedObstructionUnitOutputProbe (k : ℕ) :
    lp (fun _ : ℕ => ℝ) 2 :=
  concreteL2DiagonalWeight
      (concreteL2DiagonalUnboundednessObstructionSurface.witness k) •
    concreteL2MathlibUnit
      (concreteL2DiagonalUnboundednessObstructionSurface.witness k)

/-- The completed Hilbert norm of the obstruction output probe is the selected
positive diagonal weight. -/
theorem concrete_l2_r2_completed_obstruction_unit_output_norm_eq_weight
    (k : ℕ) :
    ‖concreteL2R2CompletedObstructionUnitOutputProbe k‖ =
      concreteL2DiagonalWeight
        (concreteL2DiagonalUnboundednessObstructionSurface.witness k) := by
  simp [concreteL2R2CompletedObstructionUnitOutputProbe,
    concrete_l2_mathlib_unit_norm_eq_one,
    abs_of_nonneg
      (le_of_lt (concrete_l2_diagonal_weight_pos
        (concreteL2DiagonalUnboundednessObstructionSurface.witness k)))]

/-- The completed Hilbert norm of the obstruction output probe exceeds the
requested threshold. -/
theorem concrete_l2_r2_completed_obstruction_unit_output_norm_gt_threshold
    (k : ℕ) :
    (k : ℝ) < ‖concreteL2R2CompletedObstructionUnitOutputProbe k‖ := by
  rw [concrete_l2_r2_completed_obstruction_unit_output_norm_eq_weight]
  exact concrete_l2_diagonal_obstruction_index_threshold_law k

/-- Public predicate for the completed Hilbert output-norm lower-bound layer. -/
def concreteL2R2CompletedUnitProbeOutputNormLowerBound : Prop :=
  ∀ k : ℕ,
    (k : ℝ) < ‖concreteL2R2CompletedObstructionUnitOutputProbe k‖

/-- The completed Hilbert output-norm lower-bound certificate is ready. -/
theorem concrete_l2_r2_completed_unit_probe_output_norm_lower_bound :
    concreteL2R2CompletedUnitProbeOutputNormLowerBound := by
  intro k
  exact concrete_l2_r2_completed_obstruction_unit_output_norm_gt_threshold k

/-- Public theorem-entry predicate for the completed unit-probe output-norm lower
bound. -/
def concreteAnalyticSpineL2R2CompletedUnitProbeOutputNormLowerBoundReady : Prop :=
  concreteAnalyticSpineL2R2UnitProbeActionMassLowerBoundReady ∧
  concreteAnalyticSpineL2MathlibNormAdapterSurfaceReady ∧
  concreteL2R2CompletedUnitProbeOutputNormLowerBound

/-- The completed unit-probe output-norm lower-bound layer is ready. -/
theorem concrete_analytic_spine_l2_r2_completed_unit_probe_output_norm_lower_bound_ready :
    concreteAnalyticSpineL2R2CompletedUnitProbeOutputNormLowerBoundReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_unit_probe_action_mass_lower_bound_ready,
    concrete_analytic_spine_l2_mathlib_norm_adapter_surface_ready,
    concrete_l2_r2_completed_unit_probe_output_norm_lower_bound⟩

end

end MathlibAnalytic
end MGAP4D
