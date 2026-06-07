import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedOperatorTopologyBranchEventualConvergenceCertificate
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedCountableAdditivityDischargeTarget

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Branch-level countable-additivity discharge packet at the current concrete
operator-topology stage.

It packages the genuine computational witness now available for the two realized
branches: an eventual-convergence certificate, exact limit-slot agreement, the
concrete operator-topology convergence target, and the canonical
countable-additivity discharge target. -/
def SpectralMeasurePVMOperatorTopologyBranchCountableAdditivityDischargeReady
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificateBridgeReady s ∧
  SpectralMeasurePVMOperatorTopologyBranchLimitSlotAgreementBridgeReady s ∧
  SpectralMeasurePVMOperatorValuedCountableAdditivityDischargeTargetReady ∧
  SpectralMeasurePVMConcreteCountableAdditivityTarget ∧
  SpectralMeasurePVMConcreteOperatorTopologyConvergenceTarget ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- A realized branch supplies the branch-level countable-additivity discharge
packet. -/
theorem spectral_measure_pvm_operator_topology_branch_countable_additivity_discharge_ready
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hcase : SpectralMeasurePVMOperatorTopologyBranchRealizationCase s) :
    SpectralMeasurePVMOperatorTopologyBranchCountableAdditivityDischargeReady s := by
  exact ⟨
    spectral_measure_pvm_operator_topology_branch_eventual_convergence_certificate_bridge_ready s hcase,
    spectral_measure_pvm_operator_topology_branch_limit_slot_agreement_bridge_ready s hcase,
    spectral_measure_pvm_operator_valued_countable_additivity_discharge_target_ready,
    spectral_measure_pvm_concrete_countable_additivity_target_ready,
    spectral_measure_pvm_concrete_operator_topology_convergence_target_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Extract the eventual-convergence certificate bridge from the branch-level
countable-additivity discharge packet. -/
theorem spectral_measure_pvm_operator_topology_branch_countable_additivity_discharge_extracts_eventual_convergence_certificate_bridge
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyBranchCountableAdditivityDischargeReady s) :
    SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificateBridgeReady s := by
  exact h.1

/-- Extract the exact limit-slot agreement bridge from the branch-level
countable-additivity discharge packet. -/
theorem spectral_measure_pvm_operator_topology_branch_countable_additivity_discharge_extracts_limit_slot_agreement_bridge
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyBranchCountableAdditivityDischargeReady s) :
    SpectralMeasurePVMOperatorTopologyBranchLimitSlotAgreementBridgeReady s := by
  exact h.2.1

/-- Extract the canonical countable-additivity discharge target from the
branch-level discharge packet. -/
theorem spectral_measure_pvm_operator_topology_branch_countable_additivity_discharge_extracts_countable_additivity_discharge_target
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyBranchCountableAdditivityDischargeReady s) :
    SpectralMeasurePVMOperatorValuedCountableAdditivityDischargeTargetReady := by
  exact h.2.2.1

/-- The canonical empty countable family has the branch-level
countable-additivity discharge packet. -/
theorem spectral_measure_pvm_operator_topology_canonical_empty_family_countable_additivity_discharge_ready :
    SpectralMeasurePVMOperatorTopologyBranchCountableAdditivityDischargeReady
      spectralMeasurePVMConcreteEmptyCountableFamily := by
  exact spectral_measure_pvm_operator_topology_branch_countable_additivity_discharge_ready
    spectralMeasurePVMConcreteEmptyCountableFamily
    spectral_measure_pvm_operator_topology_canonical_empty_family_branch_realization_case

/-- The canonical pinned single-whole family has the branch-level
countable-additivity discharge packet at any pin. -/
theorem spectral_measure_pvm_operator_topology_canonical_single_whole_family_countable_additivity_discharge_ready
    (k : Nat) :
    SpectralMeasurePVMOperatorTopologyBranchCountableAdditivityDischargeReady
      (spectralMeasurePVMConcreteSingleWholeAtFamily k) := by
  exact spectral_measure_pvm_operator_topology_branch_countable_additivity_discharge_ready
    (spectralMeasurePVMConcreteSingleWholeAtFamily k)
    (spectral_measure_pvm_operator_topology_canonical_single_whole_family_branch_realization_case k)

end

end Theorem
end R4
end MGAP4D
