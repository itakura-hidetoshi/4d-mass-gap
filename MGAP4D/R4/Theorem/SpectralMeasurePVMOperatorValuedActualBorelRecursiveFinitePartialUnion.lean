import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelCountableFamilyDisjointnessSkeleton

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Recursive finite partial union for an actual-Borel countable family.

This is the first non-placeholder finite-partial union surface.  It is still a
finite construction only; no countable union or operator-topology limit is
claimed here. -/
def spectralMeasurePVMActualBorelRecursiveFinitePartialUnion
    (F : SpectralMeasurePVMActualBorelCountableFamily) :
    ℕ → SpectralMeasurePVMActualBorelCarrierSet
  | 0 => F 0
  | n + 1 =>
      spectralMeasurePVMActualBorelCarrierSetUnion
        (spectralMeasurePVMActualBorelRecursiveFinitePartialUnion F n)
        (F (n + 1))

/-- The recursive finite partial union of the empty actual-Borel family is
extensionally empty. -/
theorem spectral_measure_pvm_actual_borel_recursive_finite_partial_union_empty_underlying
    (n : ℕ) :
    (spectralMeasurePVMActualBorelRecursiveFinitePartialUnion
        spectralMeasurePVMActualBorelEmptyCountableFamily n).1 = (∅ : Set ℝ) := by
  induction n with
  | zero =>
      simp [spectralMeasurePVMActualBorelRecursiveFinitePartialUnion,
        spectralMeasurePVMActualBorelEmptyCountableFamily,
        spectralMeasurePVMActualBorelEmptySet]
  | succ n ih =>
      simp [spectralMeasurePVMActualBorelRecursiveFinitePartialUnion,
        spectralMeasurePVMActualBorelEmptyCountableFamily,
        spectralMeasurePVMActualBorelCarrierSetUnion,
        spectralMeasurePVMActualBorelEmptySet,
        ih]

/-- The recursive finite partial union agrees extensionally with the previous
empty-family placeholder on the empty family. -/
theorem spectral_measure_pvm_actual_borel_recursive_finite_partial_union_empty_agrees_with_placeholder
    (n : ℕ) :
    (spectralMeasurePVMActualBorelRecursiveFinitePartialUnion
        spectralMeasurePVMActualBorelEmptyCountableFamily n).1 =
      (spectralMeasurePVMActualBorelFinitePartialUnion
        spectralMeasurePVMActualBorelEmptyCountableFamily n).1 := by
  rw [spectral_measure_pvm_actual_borel_recursive_finite_partial_union_empty_underlying n]
  rfl

/-- Projection of the recursive finite partial union of the empty family is
pointwise zero, by the extensional zero lemma. -/
theorem spectral_measure_pvm_actual_borel_recursive_finite_partial_union_empty_projection_zero
    (n : ℕ) (x : MathlibAnalytic.ConcreteL2R1HilbertCarrier) :
    spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        (spectralMeasurePVMActualBorelRecursiveFinitePartialUnion
          spectralMeasurePVMActualBorelEmptyCountableFamily n) x = 0 := by
  exact
    spectral_measure_pvm_actual_borel_endpoint_seeded_projection_map_apply_eq_zero_of_underlying_empty
      (spectralMeasurePVMActualBorelRecursiveFinitePartialUnion
        spectralMeasurePVMActualBorelEmptyCountableFamily n)
      (spectral_measure_pvm_actual_borel_recursive_finite_partial_union_empty_underlying n)
      x

/-- Recursive finite-partial-union target for the actual-Borel carrier. -/
def SpectralMeasurePVMActualBorelRecursiveFinitePartialUnionTarget : Prop :=
  (∀ n : ℕ,
    (spectralMeasurePVMActualBorelRecursiveFinitePartialUnion
        spectralMeasurePVMActualBorelEmptyCountableFamily n).1 = (∅ : Set ℝ)) ∧
  (∀ n : ℕ,
    (spectralMeasurePVMActualBorelRecursiveFinitePartialUnion
        spectralMeasurePVMActualBorelEmptyCountableFamily n).1 =
      (spectralMeasurePVMActualBorelFinitePartialUnion
        spectralMeasurePVMActualBorelEmptyCountableFamily n).1) ∧
  (∀ n : ℕ, ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        (spectralMeasurePVMActualBorelRecursiveFinitePartialUnion
          spectralMeasurePVMActualBorelEmptyCountableFamily n) x = 0)

/-- The recursive finite-partial-union target is ready. -/
theorem spectral_measure_pvm_actual_borel_recursive_finite_partial_union_target_ready :
    SpectralMeasurePVMActualBorelRecursiveFinitePartialUnionTarget := by
  exact ⟨
    spectral_measure_pvm_actual_borel_recursive_finite_partial_union_empty_underlying,
    spectral_measure_pvm_actual_borel_recursive_finite_partial_union_empty_agrees_with_placeholder,
    spectral_measure_pvm_actual_borel_recursive_finite_partial_union_empty_projection_zero⟩

/-- Actual-Borel recursive finite-partial-union bridge. -/
def SpectralMeasurePVMActualBorelRecursiveFinitePartialUnionBridgeReady : Prop :=
  SpectralMeasurePVMActualBorelCountableFamilyDisjointnessSkeletonPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelProjectionMapExtensionalRegressionGuard ∧
  SpectralMeasurePVMActualBorelRecursiveFinitePartialUnionTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual-Borel recursive finite-partial-union bridge is ready. -/
theorem spectral_measure_pvm_actual_borel_recursive_finite_partial_union_bridge_ready :
    SpectralMeasurePVMActualBorelRecursiveFinitePartialUnionBridgeReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_countable_family_disjointness_skeleton_public_boundary_held,
    spectral_measure_pvm_actual_borel_projection_map_extensional_regression_guard_ready,
    spectral_measure_pvm_actual_borel_recursive_finite_partial_union_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after the actual-Borel recursive finite-partial-union bridge. -/
def SpectralMeasurePVMActualBorelRecursiveFinitePartialUnionPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelRecursiveFinitePartialUnionBridgeReady ∧
  SpectralMeasurePVMActualBorelRecursiveFinitePartialUnionTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the actual-Borel recursive finite-partial-union bridge is held. -/
theorem spectral_measure_pvm_actual_borel_recursive_finite_partial_union_public_boundary_held :
    SpectralMeasurePVMActualBorelRecursiveFinitePartialUnionPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_recursive_finite_partial_union_bridge_ready,
    spectral_measure_pvm_actual_borel_recursive_finite_partial_union_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
