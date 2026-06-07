import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedOperatorTopologyBranchDischargeFromCertificate

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Branch-level bridge from the concrete eventual-convergence certificate to the
existing genuine operator-topology countable-additivity bridge.

This does not claim the final Hilbert-space strong/weak operator-topology theorem.
It records that, for a realized concrete branch, the explicit eventual-tail
certificate, the concrete discharge target, and the already-established genuine
bridge interface are all available together, with the no-shell-collapse boundary
preserved. -/
def SpectralMeasurePVMOperatorTopologyBranchGenuineBridgeFromCertificateReady
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  SpectralMeasurePVMOperatorTopologyBranchDischargeFromCertificateReady s ∧
  (∃ w : SpectralMeasurePVMOperatorTopologyCountableAdditivityRealizationWitness,
    SpectralMeasurePVMOperatorTopologyCountableAdditivityConditionalBridgeReady w) ∧
  SpectralMeasurePVMOperatorValuedGenuineOperatorTopologyCountableAdditivityBridgeReady ∧
  SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificateBridgeReady s ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- A realized concrete branch supplies the genuine-bridge-from-certificate
surface. -/
theorem spectral_measure_pvm_operator_topology_branch_genuine_bridge_from_certificate_ready
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hcase : SpectralMeasurePVMOperatorTopologyBranchRealizationCase s) :
    SpectralMeasurePVMOperatorTopologyBranchGenuineBridgeFromCertificateReady s := by
  exact ⟨
    spectral_measure_pvm_operator_topology_branch_discharge_from_certificate_ready s hcase,
    spectral_measure_pvm_operator_topology_branch_realization_case_conditional_bridge_ready s hcase,
    spectral_measure_pvm_operator_valued_genuine_operator_topology_countable_additivity_bridge_ready,
    spectral_measure_pvm_operator_topology_branch_eventual_convergence_certificate_bridge_ready s hcase,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The canonical empty countable family supplies the genuine-bridge-from-
certificate surface. -/
theorem spectral_measure_pvm_operator_topology_canonical_empty_family_genuine_bridge_from_certificate_ready :
    SpectralMeasurePVMOperatorTopologyBranchGenuineBridgeFromCertificateReady
      spectralMeasurePVMConcreteEmptyCountableFamily := by
  exact spectral_measure_pvm_operator_topology_branch_genuine_bridge_from_certificate_ready
    spectralMeasurePVMConcreteEmptyCountableFamily
    spectral_measure_pvm_operator_topology_canonical_empty_family_branch_realization_case

/-- The canonical pinned single-whole family supplies the genuine-bridge-from-
certificate surface at any pin. -/
theorem spectral_measure_pvm_operator_topology_canonical_single_whole_family_genuine_bridge_from_certificate_ready
    (k : Nat) :
    SpectralMeasurePVMOperatorTopologyBranchGenuineBridgeFromCertificateReady
      (spectralMeasurePVMConcreteSingleWholeAtFamily k) := by
  exact spectral_measure_pvm_operator_topology_branch_genuine_bridge_from_certificate_ready
    (spectralMeasurePVMConcreteSingleWholeAtFamily k)
    (spectral_measure_pvm_operator_topology_canonical_single_whole_family_branch_realization_case k)

/-- Projection: the genuine-bridge-from-certificate surface exposes the concrete
branch discharge. -/
theorem spectral_measure_pvm_operator_topology_branch_genuine_bridge_from_certificate_extracts_discharge
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyBranchGenuineBridgeFromCertificateReady s) :
    SpectralMeasurePVMOperatorTopologyBranchDischargeFromCertificateReady s := by
  rcases h with ⟨hdischarge, _, _, _, _⟩
  exact hdischarge

/-- Projection: the genuine-bridge-from-certificate surface exposes a branch-
specific conditional realization witness. -/
theorem spectral_measure_pvm_operator_topology_branch_genuine_bridge_from_certificate_extracts_conditional_witness
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyBranchGenuineBridgeFromCertificateReady s) :
    ∃ w : SpectralMeasurePVMOperatorTopologyCountableAdditivityRealizationWitness,
      SpectralMeasurePVMOperatorTopologyCountableAdditivityConditionalBridgeReady w := by
  rcases h with ⟨_, hwitness, _, _, _⟩
  exact hwitness

/-- Projection: the genuine-bridge-from-certificate surface exposes the genuine
operator-topology countable-additivity bridge interface. -/
theorem spectral_measure_pvm_operator_topology_branch_genuine_bridge_from_certificate_extracts_genuine_bridge
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyBranchGenuineBridgeFromCertificateReady s) :
    SpectralMeasurePVMOperatorValuedGenuineOperatorTopologyCountableAdditivityBridgeReady := by
  rcases h with ⟨_, _, hgenuine, _, _⟩
  exact hgenuine

/-- Projection: the genuine-bridge-from-certificate surface keeps the no-shell-
collapse boundary. -/
theorem spectral_measure_pvm_operator_topology_branch_genuine_bridge_from_certificate_preserves_no_shell_collapse
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyBranchGenuineBridgeFromCertificateReady s) :
    SpectralMeasurePVMNoShellToFullCollapseBoundary := by
  rcases h with ⟨_, _, _, _, hboundary⟩
  exact hboundary

end

end Theorem
end R4
end MGAP4D
