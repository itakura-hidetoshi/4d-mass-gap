import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedOperatorTopologySingleWholeRealizationWitness

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Concrete branch cases for the current R4 operator-topology
countable-additivity surface.

At this stage the concrete surface has two realized branches: the all-empty
branch and the pinned single-whole branch.  This disjunction is not a claim that
all future R4 countable families are exhausted by these two shapes; it is the
case split for the concrete two-branch surface already constructed. -/
inductive SpectralMeasurePVMOperatorTopologyBranchRealizationCase
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop where
  | allEmpty :
      SpectralMeasurePVMConcreteAllEmptyFamily s →
      SpectralMeasurePVMOperatorTopologyBranchRealizationCase s
  | singleWholeAt :
      (k : Nat) →
      SpectralMeasurePVMConcreteSingleWholeAt s k →
      SpectralMeasurePVMOperatorTopologyBranchRealizationCase s

/-- The all-empty branch realizes the branch case split. -/
theorem spectral_measure_pvm_operator_topology_branch_realization_case_all_empty
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hs : SpectralMeasurePVMConcreteAllEmptyFamily s) :
    SpectralMeasurePVMOperatorTopologyBranchRealizationCase s := by
  exact SpectralMeasurePVMOperatorTopologyBranchRealizationCase.allEmpty hs

/-- The pinned single-whole branch realizes the branch case split. -/
theorem spectral_measure_pvm_operator_topology_branch_realization_case_single_whole
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (k : Nat)
    (hs : SpectralMeasurePVMConcreteSingleWholeAt s k) :
    SpectralMeasurePVMOperatorTopologyBranchRealizationCase s := by
  exact SpectralMeasurePVMOperatorTopologyBranchRealizationCase.singleWholeAt k hs

/-- From the current concrete branch case split, obtain the corresponding
conditional operator-topology countable-additivity bridge for the realized
branch.

The result is existential because the realization witness differs by branch:
all-empty uses the zero finite-partial sequence, while single-whole uses the
identity finite-partial sequence at the support successor. -/
theorem spectral_measure_pvm_operator_topology_branch_realization_case_conditional_bridge_ready
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hcase : SpectralMeasurePVMOperatorTopologyBranchRealizationCase s) :
    ∃ w : SpectralMeasurePVMOperatorTopologyCountableAdditivityRealizationWitness,
      SpectralMeasurePVMOperatorTopologyCountableAdditivityConditionalBridgeReady w := by
  cases hcase with
  | allEmpty hs =>
      exact ⟨
        spectralMeasurePVMOperatorTopologyAllEmptyRealizationWitness s hs,
        spectral_measure_pvm_operator_topology_all_empty_conditional_bridge_ready s hs⟩
  | singleWholeAt k hs =>
      exact ⟨
        spectralMeasurePVMOperatorTopologySingleWholeRealizationWitness s k hs,
        spectral_measure_pvm_operator_topology_single_whole_conditional_bridge_ready s k hs⟩

/-- The canonical empty countable family enters the branch case split. -/
theorem spectral_measure_pvm_operator_topology_canonical_empty_family_branch_realization_case :
    SpectralMeasurePVMOperatorTopologyBranchRealizationCase
      spectralMeasurePVMConcreteEmptyCountableFamily := by
  exact spectral_measure_pvm_operator_topology_branch_realization_case_all_empty
    spectralMeasurePVMConcreteEmptyCountableFamily
    spectral_measure_pvm_concrete_empty_countable_family_all_empty

/-- The canonical pinned single-whole family enters the branch case split at its
pin. -/
theorem spectral_measure_pvm_operator_topology_canonical_single_whole_family_branch_realization_case
    (k : Nat) :
    SpectralMeasurePVMOperatorTopologyBranchRealizationCase
      (spectralMeasurePVMConcreteSingleWholeAtFamily k) := by
  exact spectral_measure_pvm_operator_topology_branch_realization_case_single_whole
    (spectralMeasurePVMConcreteSingleWholeAtFamily k) k
    (spectral_measure_pvm_concrete_single_whole_at_family_spec k)

/-- The canonical empty countable family has a branch-realized conditional
operator-topology bridge. -/
theorem spectral_measure_pvm_operator_topology_canonical_empty_family_branch_bridge_ready :
    ∃ w : SpectralMeasurePVMOperatorTopologyCountableAdditivityRealizationWitness,
      SpectralMeasurePVMOperatorTopologyCountableAdditivityConditionalBridgeReady w := by
  exact spectral_measure_pvm_operator_topology_branch_realization_case_conditional_bridge_ready
    spectralMeasurePVMConcreteEmptyCountableFamily
    spectral_measure_pvm_operator_topology_canonical_empty_family_branch_realization_case

/-- The canonical pinned single-whole family has a branch-realized conditional
operator-topology bridge at any pin. -/
theorem spectral_measure_pvm_operator_topology_canonical_single_whole_family_branch_bridge_ready
    (k : Nat) :
    ∃ w : SpectralMeasurePVMOperatorTopologyCountableAdditivityRealizationWitness,
      SpectralMeasurePVMOperatorTopologyCountableAdditivityConditionalBridgeReady w := by
  exact spectral_measure_pvm_operator_topology_branch_realization_case_conditional_bridge_ready
    (spectralMeasurePVMConcreteSingleWholeAtFamily k)
    (spectral_measure_pvm_operator_topology_canonical_single_whole_family_branch_realization_case k)

end

end Theorem
end R4
end MGAP4D
