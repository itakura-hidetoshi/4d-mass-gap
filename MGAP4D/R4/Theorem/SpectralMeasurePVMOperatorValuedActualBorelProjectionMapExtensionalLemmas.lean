import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelCountableAdditivityPreparation

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Extensional zero law for the endpoint-seeded actual-Borel projection map.

Use this lemma instead of relying on definitional equality of subtype witnesses. -/
theorem spectral_measure_pvm_actual_borel_endpoint_seeded_projection_map_eq_zero_of_underlying_empty
    (s : SpectralMeasurePVMActualBorelCarrierSet)
    (hs : s.1 = (∅ : Set ℝ)) :
    spectralMeasurePVMActualBorelEndpointSeededProjectionMap s = 0 := by
  simp [spectralMeasurePVMActualBorelEndpointSeededProjectionMap, hs]

/-- Pointwise extensional zero law for the endpoint-seeded actual-Borel projection map. -/
theorem spectral_measure_pvm_actual_borel_endpoint_seeded_projection_map_apply_eq_zero_of_underlying_empty
    (s : SpectralMeasurePVMActualBorelCarrierSet)
    (hs : s.1 = (∅ : Set ℝ))
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMActualBorelEndpointSeededProjectionMap s x = 0 := by
  rw [spectral_measure_pvm_actual_borel_endpoint_seeded_projection_map_eq_zero_of_underlying_empty s hs]
  rfl

/-- Extensional identity law for the endpoint-seeded actual-Borel projection map. -/
theorem spectral_measure_pvm_actual_borel_endpoint_seeded_projection_map_eq_id_of_underlying_ne_empty
    (s : SpectralMeasurePVMActualBorelCarrierSet)
    (hs : s.1 ≠ (∅ : Set ℝ)) :
    spectralMeasurePVMActualBorelEndpointSeededProjectionMap s =
      ContinuousLinearMap.id ℝ MathlibAnalytic.ConcreteL2R1HilbertCarrier := by
  simp [spectralMeasurePVMActualBorelEndpointSeededProjectionMap, hs]

/-- Pointwise extensional identity law for the endpoint-seeded actual-Borel projection map. -/
theorem spectral_measure_pvm_actual_borel_endpoint_seeded_projection_map_apply_eq_self_of_underlying_ne_empty
    (s : SpectralMeasurePVMActualBorelCarrierSet)
    (hs : s.1 ≠ (∅ : Set ℝ))
    (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMActualBorelEndpointSeededProjectionMap s x = x := by
  rw [spectral_measure_pvm_actual_borel_endpoint_seeded_projection_map_eq_id_of_underlying_ne_empty s hs]
  rfl

/-- Empty finite partial unions are extensionally empty. -/
theorem spectral_measure_pvm_actual_borel_empty_family_finite_partial_underlying_empty
    (n : ℕ) :
    (spectralMeasurePVMActualBorelFinitePartialUnion
        spectralMeasurePVMActualBorelEmptyCountableFamily n).1 = (∅ : Set ℝ) := by
  rfl

/-- Empty finite partial projections are zero, using the extensional zero law. -/
theorem spectral_measure_pvm_actual_borel_empty_family_finite_partial_projection_zero_ext
    (n : ℕ) (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        (spectralMeasurePVMActualBorelFinitePartialUnion
          spectralMeasurePVMActualBorelEmptyCountableFamily n) x = 0 := by
  exact
    spectral_measure_pvm_actual_borel_endpoint_seeded_projection_map_apply_eq_zero_of_underlying_empty
      (spectralMeasurePVMActualBorelFinitePartialUnion
        spectralMeasurePVMActualBorelEmptyCountableFamily n)
      (spectral_measure_pvm_actual_borel_empty_family_finite_partial_underlying_empty n)
      x

/-- Regression guard: future actual-Borel projection-map proofs should use the
extensional zero/identity lemmas above, not `rfl` through subtype witnesses. -/
def SpectralMeasurePVMActualBorelProjectionMapExtensionalRegressionGuard : Prop :=
  (∀ n : ℕ, ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        (spectralMeasurePVMActualBorelFinitePartialUnion
          spectralMeasurePVMActualBorelEmptyCountableFamily n) x = 0) ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual-Borel projection-map extensional regression guard is ready. -/
theorem spectral_measure_pvm_actual_borel_projection_map_extensional_regression_guard_ready :
    SpectralMeasurePVMActualBorelProjectionMapExtensionalRegressionGuard := by
  exact ⟨
    spectral_measure_pvm_actual_borel_empty_family_finite_partial_projection_zero_ext,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
