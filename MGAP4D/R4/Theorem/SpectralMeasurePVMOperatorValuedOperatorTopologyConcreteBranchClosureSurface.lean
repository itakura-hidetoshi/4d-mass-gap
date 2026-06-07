import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedOperatorTopologyBranchGenuineBridgeFromCertificate

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Concrete branch closure surface for the R4 operator-topology
countable-additivity route.

This is the first compact closure surface after the explicit branch
realization/certificate chain.  It gathers the branch realization case, the
finite-tail convergence certificate, the concrete countable-additivity target,
the concrete operator-topology convergence target, and the genuine bridge
interface, while explicitly keeping the no-shell-collapse boundary. -/
def SpectralMeasurePVMOperatorTopologyConcreteBranchClosureSurfaceReady
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  SpectralMeasurePVMOperatorTopologyBranchEventualConstancy s ∧
  SpectralMeasurePVMOperatorTopologyBranchLimitSlotAgreement s ∧
  SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificateBridgeReady s ∧
  SpectralMeasurePVMOperatorTopologyBranchDischargeFromCertificateReady s ∧
  SpectralMeasurePVMOperatorTopologyBranchGenuineBridgeFromCertificateReady s ∧
  SpectralMeasurePVMConcreteCountableAdditivityTarget ∧
  SpectralMeasurePVMConcreteOperatorTopologyConvergenceTarget ∧
  SpectralMeasurePVMOperatorValuedGenuineOperatorTopologyCountableAdditivityBridgeReady ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- A realized concrete branch closes the concrete operator-topology branch
surface. -/
theorem spectral_measure_pvm_operator_topology_concrete_branch_closure_surface_ready
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hcase : SpectralMeasurePVMOperatorTopologyBranchRealizationCase s) :
    SpectralMeasurePVMOperatorTopologyConcreteBranchClosureSurfaceReady s := by
  exact ⟨
    spectral_measure_pvm_operator_topology_branch_realization_case_eventual_constancy s hcase,
    spectral_measure_pvm_operator_topology_branch_realization_case_limit_slot_agreement s hcase,
    spectral_measure_pvm_operator_topology_branch_eventual_convergence_certificate_bridge_ready s hcase,
    spectral_measure_pvm_operator_topology_branch_discharge_from_certificate_ready s hcase,
    spectral_measure_pvm_operator_topology_branch_genuine_bridge_from_certificate_ready s hcase,
    spectral_measure_pvm_concrete_countable_additivity_target_ready,
    spectral_measure_pvm_concrete_operator_topology_convergence_target_ready,
    spectral_measure_pvm_operator_valued_genuine_operator_topology_countable_additivity_bridge_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The canonical empty countable family closes the concrete branch surface. -/
theorem spectral_measure_pvm_operator_topology_canonical_empty_family_concrete_branch_closure_surface_ready :
    SpectralMeasurePVMOperatorTopologyConcreteBranchClosureSurfaceReady
      spectralMeasurePVMConcreteEmptyCountableFamily := by
  exact spectral_measure_pvm_operator_topology_concrete_branch_closure_surface_ready
    spectralMeasurePVMConcreteEmptyCountableFamily
    spectral_measure_pvm_operator_topology_canonical_empty_family_branch_realization_case

/-- The canonical pinned single-whole family closes the concrete branch surface
at any pin. -/
theorem spectral_measure_pvm_operator_topology_canonical_single_whole_family_concrete_branch_closure_surface_ready
    (k : Nat) :
    SpectralMeasurePVMOperatorTopologyConcreteBranchClosureSurfaceReady
      (spectralMeasurePVMConcreteSingleWholeAtFamily k) := by
  exact spectral_measure_pvm_operator_topology_concrete_branch_closure_surface_ready
    (spectralMeasurePVMConcreteSingleWholeAtFamily k)
    (spectral_measure_pvm_operator_topology_canonical_single_whole_family_branch_realization_case k)

/-- Projection: the concrete branch closure surface exposes branch eventual
constancy. -/
theorem spectral_measure_pvm_operator_topology_concrete_branch_closure_surface_extracts_eventual_constancy
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyConcreteBranchClosureSurfaceReady s) :
    SpectralMeasurePVMOperatorTopologyBranchEventualConstancy s := by
  rcases h with ⟨heventual, _, _, _, _, _, _, _, _⟩
  exact heventual

/-- Projection: the concrete branch closure surface exposes branch limit-slot
agreement. -/
theorem spectral_measure_pvm_operator_topology_concrete_branch_closure_surface_extracts_limit_slot_agreement
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyConcreteBranchClosureSurfaceReady s) :
    SpectralMeasurePVMOperatorTopologyBranchLimitSlotAgreement s := by
  rcases h with ⟨_, hagree, _, _, _, _, _, _, _⟩
  exact hagree

/-- Projection: the concrete branch closure surface exposes the certificate
bridge. -/
theorem spectral_measure_pvm_operator_topology_concrete_branch_closure_surface_extracts_certificate_bridge
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyConcreteBranchClosureSurfaceReady s) :
    SpectralMeasurePVMOperatorTopologyBranchEventualConvergenceCertificateBridgeReady s := by
  rcases h with ⟨_, _, hcert, _, _, _, _, _, _⟩
  exact hcert

/-- Projection: the concrete branch closure surface exposes the genuine bridge
interface. -/
theorem spectral_measure_pvm_operator_topology_concrete_branch_closure_surface_extracts_genuine_bridge
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyConcreteBranchClosureSurfaceReady s) :
    SpectralMeasurePVMOperatorValuedGenuineOperatorTopologyCountableAdditivityBridgeReady := by
  rcases h with ⟨_, _, _, _, _, _, _, hgenuine, _⟩
  exact hgenuine

/-- Projection: the concrete branch closure surface preserves the no-shell-
collapse boundary. -/
theorem spectral_measure_pvm_operator_topology_concrete_branch_closure_surface_preserves_no_shell_collapse
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyConcreteBranchClosureSurfaceReady s) :
    SpectralMeasurePVMNoShellToFullCollapseBoundary := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hboundary⟩
  exact hboundary

end

end Theorem
end R4
end MGAP4D
