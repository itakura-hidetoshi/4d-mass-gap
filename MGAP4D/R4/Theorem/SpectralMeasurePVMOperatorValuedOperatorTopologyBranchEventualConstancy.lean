import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedOperatorTopologySingleWholeEventualConstancy

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Unified eventual-constancy target for the two currently realized concrete
operator-topology branches.

The all-empty branch is constantly zero from the start.  The pinned single-whole
branch is eventually constantly identity after the successor of the pinned
support. -/
def SpectralMeasurePVMOperatorTopologyBranchEventualConstancy
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  (SpectralMeasurePVMConcreteAllEmptyFamily s ∧
    ∀ N : Nat,
      spectralMeasurePVMConcreteNormalizationCandidate
          (SpectralMeasurePVMConcreteFinitePartialUnion N s) =
        SpectralMeasurePVMConcreteBoundedOperator.zero) ∨
  (∃ k : Nat,
    SpectralMeasurePVMConcreteSingleWholeAt s k ∧
      SpectralMeasurePVMOperatorTopologySingleWholeEventuallyConstantIdentitySequence s k)

/-- The all-empty branch is constantly zero from the start. -/
theorem spectral_measure_pvm_operator_topology_all_empty_branch_eventual_constancy
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hs : SpectralMeasurePVMConcreteAllEmptyFamily s) :
    SpectralMeasurePVMOperatorTopologyBranchEventualConstancy s := by
  exact Or.inl ⟨hs, spectral_measure_pvm_concrete_partial_sum_all_empty_zero s hs⟩

/-- The pinned single-whole branch is eventually constantly identity after its
support. -/
theorem spectral_measure_pvm_operator_topology_single_whole_branch_eventual_constancy
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (k : Nat)
    (hs : SpectralMeasurePVMConcreteSingleWholeAt s k) :
    SpectralMeasurePVMOperatorTopologyBranchEventualConstancy s := by
  exact Or.inr ⟨k, hs,
    spectral_measure_pvm_operator_topology_single_whole_eventually_constant_identity_sequence_ready s k hs⟩

/-- Every realized concrete operator-topology branch has an explicit eventual
constancy description. -/
theorem spectral_measure_pvm_operator_topology_branch_realization_case_eventual_constancy
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hcase : SpectralMeasurePVMOperatorTopologyBranchRealizationCase s) :
    SpectralMeasurePVMOperatorTopologyBranchEventualConstancy s := by
  cases hcase with
  | allEmpty hs =>
      exact spectral_measure_pvm_operator_topology_all_empty_branch_eventual_constancy s hs
  | singleWholeAt k hs =>
      exact spectral_measure_pvm_operator_topology_single_whole_branch_eventual_constancy s k hs

/-- A branch with eventual constancy and a realized branch case has a conditional
operator-topology countable-additivity bridge.  The bridge still carries the
branch-specific realization witness, while the eventual-constancy target records
the shape of the finite partial operator sequence. -/
def SpectralMeasurePVMOperatorTopologyBranchEventualConstancyBridgeReady
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  SpectralMeasurePVMOperatorTopologyBranchEventualConstancy s ∧
  ∃ w : SpectralMeasurePVMOperatorTopologyCountableAdditivityRealizationWitness,
    SpectralMeasurePVMOperatorTopologyCountableAdditivityConditionalBridgeReady w

/-- A realized concrete branch supplies both eventual constancy and a conditional
operator-topology countable-additivity bridge. -/
theorem spectral_measure_pvm_operator_topology_branch_eventual_constancy_bridge_ready
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hcase : SpectralMeasurePVMOperatorTopologyBranchRealizationCase s) :
    SpectralMeasurePVMOperatorTopologyBranchEventualConstancyBridgeReady s := by
  exact ⟨
    spectral_measure_pvm_operator_topology_branch_realization_case_eventual_constancy s hcase,
    spectral_measure_pvm_operator_topology_branch_realization_case_conditional_bridge_ready s hcase⟩

/-- The canonical empty countable family has the unified branch-eventual-constancy
bridge. -/
theorem spectral_measure_pvm_operator_topology_canonical_empty_family_branch_eventual_constancy_bridge_ready :
    SpectralMeasurePVMOperatorTopologyBranchEventualConstancyBridgeReady
      spectralMeasurePVMConcreteEmptyCountableFamily := by
  exact spectral_measure_pvm_operator_topology_branch_eventual_constancy_bridge_ready
    spectralMeasurePVMConcreteEmptyCountableFamily
    spectral_measure_pvm_operator_topology_canonical_empty_family_branch_realization_case

/-- The canonical pinned single-whole family has the unified
branch-eventual-constancy bridge at any pin. -/
theorem spectral_measure_pvm_operator_topology_canonical_single_whole_family_branch_eventual_constancy_bridge_ready
    (k : Nat) :
    SpectralMeasurePVMOperatorTopologyBranchEventualConstancyBridgeReady
      (spectralMeasurePVMConcreteSingleWholeAtFamily k) := by
  exact spectral_measure_pvm_operator_topology_branch_eventual_constancy_bridge_ready
    (spectralMeasurePVMConcreteSingleWholeAtFamily k)
    (spectral_measure_pvm_operator_topology_canonical_single_whole_family_branch_realization_case k)

end

end Theorem
end R4
end MGAP4D
