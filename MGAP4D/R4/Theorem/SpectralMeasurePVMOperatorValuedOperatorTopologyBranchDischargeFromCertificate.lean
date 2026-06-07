import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedOperatorTopologyBranchEventualConvergenceCertificate

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Branch-level discharge packet extracted from an eventual-convergence
certificate.

This is still a concrete two-branch R4 discharge, not the final Hilbert-space
strong/weak operator-topology theorem.  Its role is to connect the explicit
finite-tail agreement certificate to the existing countable-additivity discharge
target fields. -/
def SpectralMeasurePVMOperatorTopologyBranchDischargeFromCertificateReady
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificateBridgeReady s ∧
  SpectralMeasurePVMOperatorValuedCountableAdditivityDischargeTargetReady ∧
  SpectralMeasurePVMConcreteFinitePartialSumSequenceTarget ∧
  SpectralMeasurePVMConcreteOperatorTopologyConvergenceTarget ∧
  SpectralMeasurePVMConcreteCountableAdditivityTarget ∧
  SpectralMeasurePVMConcreteSigmaAdditivityReceiptTarget ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- A realized branch discharges the concrete operator-topology countable
additivity route from its eventual-convergence certificate. -/
theorem spectral_measure_pvm_operator_topology_branch_discharge_from_certificate_ready
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hcase : SpectralMeasurePVMOperatorTopologyBranchRealizationCase s) :
    SpectralMeasurePVMOperatorTopologyBranchDischargeFromCertificateReady s := by
  exact ⟨
    spectral_measure_pvm_operator_topology_branch_eventual_convergence_certificate_bridge_ready s hcase,
    spectral_measure_pvm_operator_valued_countable_additivity_discharge_target_ready,
    spectral_measure_pvm_concrete_finite_partial_sum_sequence_target_ready,
    spectral_measure_pvm_concrete_operator_topology_convergence_target_ready,
    spectral_measure_pvm_concrete_countable_additivity_target_ready,
    spectral_measure_pvm_concrete_sigma_additivity_receipt_target_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The canonical empty family discharges the concrete operator-topology route
from its eventual-convergence certificate. -/
theorem spectral_measure_pvm_operator_topology_canonical_empty_family_discharge_from_certificate_ready :
    SpectralMeasurePVMOperatorTopologyBranchDischargeFromCertificateReady
      spectralMeasurePVMConcreteEmptyCountableFamily := by
  exact spectral_measure_pvm_operator_topology_branch_discharge_from_certificate_ready
    spectralMeasurePVMConcreteEmptyCountableFamily
    spectral_measure_pvm_operator_topology_canonical_empty_family_branch_realization_case

/-- The canonical pinned single-whole family discharges the concrete
operator-topology route from its eventual-convergence certificate at any pin. -/
theorem spectral_measure_pvm_operator_topology_canonical_single_whole_family_discharge_from_certificate_ready
    (k : Nat) :
    SpectralMeasurePVMOperatorTopologyBranchDischargeFromCertificateReady
      (spectralMeasurePVMConcreteSingleWholeAtFamily k) := by
  exact spectral_measure_pvm_operator_topology_branch_discharge_from_certificate_ready
    (spectralMeasurePVMConcreteSingleWholeAtFamily k)
    (spectral_measure_pvm_operator_topology_canonical_single_whole_family_branch_realization_case k)

/-- Projection: the branch discharge exposes the countable-additivity equation
target. -/
theorem spectral_measure_pvm_operator_topology_branch_discharge_from_certificate_extracts_countable_additivity_target
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyBranchDischargeFromCertificateReady s) :
    SpectralMeasurePVMConcreteCountableAdditivityTarget := by
  rcases h with ⟨_, _, _, _, hcountable, _, _⟩
  exact hcountable

/-- Projection: the branch discharge exposes the operator-topology convergence
target supported by the eventual-convergence certificate. -/
theorem spectral_measure_pvm_operator_topology_branch_discharge_from_certificate_extracts_operator_topology_convergence_target
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyBranchDischargeFromCertificateReady s) :
    SpectralMeasurePVMConcreteOperatorTopologyConvergenceTarget := by
  rcases h with ⟨_, _, _, hconv, _, _, _⟩
  exact hconv

/-- Projection: the branch discharge keeps the no-shell-collapse boundary. -/
theorem spectral_measure_pvm_operator_topology_branch_discharge_from_certificate_preserves_no_shell_collapse
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyBranchDischargeFromCertificateReady s) :
    SpectralMeasurePVMNoShellToFullCollapseBoundary := by
  rcases h with ⟨_, _, _, _, _, _, hboundary⟩
  exact hboundary

end

end Theorem
end R4
end MGAP4D
