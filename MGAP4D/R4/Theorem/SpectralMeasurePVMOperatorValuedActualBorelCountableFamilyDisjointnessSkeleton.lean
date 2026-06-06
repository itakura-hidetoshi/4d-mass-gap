import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelProjectionMapExtensionalLemmas

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Pairwise disjointness for countable actual-Borel families, stated
extensionally on the underlying subsets of `ℝ`. -/
def SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint
    (F : SpectralMeasurePVMActualBorelCountableFamily) : Prop :=
  ∀ i j : ℕ, i ≠ j → (F i).1 ∩ (F j).1 = (∅ : Set ℝ)

/-- The empty countable family is pairwise disjoint. -/
theorem spectral_measure_pvm_actual_borel_empty_countable_family_pairwise_disjoint :
    SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint
      spectralMeasurePVMActualBorelEmptyCountableFamily := by
  intro i j _hij
  simp [spectralMeasurePVMActualBorelEmptyCountableFamily,
    spectralMeasurePVMActualBorelEmptySet]

/-- Disjointness skeleton target for actual-Borel countable families.

This is still only a family-level skeleton: it records pairwise disjointness of
the empty family and does not assert countable union realization or
operator-topology convergence. -/
def SpectralMeasurePVMActualBorelCountableFamilyDisjointnessSkeletonTarget : Prop :=
  SpectralMeasurePVMActualBorelCountableFamilyPairwiseDisjoint
    spectralMeasurePVMActualBorelEmptyCountableFamily ∧
  (∀ n : ℕ, ∀ x : MathlibAnalytic.ConcreteL2R1HilbertCarrier,
    spectralMeasurePVMActualBorelEndpointSeededProjectionMap
        (spectralMeasurePVMActualBorelFinitePartialUnion
          spectralMeasurePVMActualBorelEmptyCountableFamily n) x = 0)

/-- The actual-Borel countable-family disjointness skeleton target is ready. -/
theorem spectral_measure_pvm_actual_borel_countable_family_disjointness_skeleton_target_ready :
    SpectralMeasurePVMActualBorelCountableFamilyDisjointnessSkeletonTarget := by
  exact ⟨
    spectral_measure_pvm_actual_borel_empty_countable_family_pairwise_disjoint,
    spectral_measure_pvm_actual_borel_empty_family_finite_partial_projection_zero_ext⟩

/-- Actual-Borel countable-family disjointness skeleton bridge. -/
def SpectralMeasurePVMActualBorelCountableFamilyDisjointnessSkeletonBridgeReady : Prop :=
  SpectralMeasurePVMActualBorelCountableAdditivityPreparationPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelProjectionMapExtensionalRegressionGuard ∧
  SpectralMeasurePVMActualBorelCountableFamilyDisjointnessSkeletonTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMGenuineSelfAdjointSpectralTheoremStillOpen ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual-Borel countable-family disjointness skeleton bridge is ready. -/
theorem spectral_measure_pvm_actual_borel_countable_family_disjointness_skeleton_bridge_ready :
    SpectralMeasurePVMActualBorelCountableFamilyDisjointnessSkeletonBridgeReady := by
  exact ⟨
    spectral_measure_pvm_actual_borel_countable_additivity_preparation_public_boundary_held,
    spectral_measure_pvm_actual_borel_projection_map_extensional_regression_guard_ready,
    spectral_measure_pvm_actual_borel_countable_family_disjointness_skeleton_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_genuine_self_adjoint_spectral_theorem_still_open_ready,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary after the actual-Borel countable-family disjointness skeleton. -/
def SpectralMeasurePVMActualBorelCountableFamilyDisjointnessSkeletonPublicBoundaryHeld : Prop :=
  SpectralMeasurePVMActualBorelCountableFamilyDisjointnessSkeletonBridgeReady ∧
  SpectralMeasurePVMActualBorelCountableFamilyDisjointnessSkeletonTarget ∧
  SpectralMeasurePVMGenuineOperatorTopologyCountableAdditivityStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary after the actual-Borel countable-family disjointness skeleton is held. -/
theorem spectral_measure_pvm_actual_borel_countable_family_disjointness_skeleton_public_boundary_held :
    SpectralMeasurePVMActualBorelCountableFamilyDisjointnessSkeletonPublicBoundaryHeld := by
  exact ⟨
    spectral_measure_pvm_actual_borel_countable_family_disjointness_skeleton_bridge_ready,
    spectral_measure_pvm_actual_borel_countable_family_disjointness_skeleton_target_ready,
    spectral_measure_pvm_genuine_operator_topology_countable_additivity_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R4
end MGAP4D
