import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedOperatorTopologyR4ConcreteRouteTopLevelChainIndex

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Canonical projection matrix extracted from the top-level concrete route
chain index.

This matrix makes the root-facing chain index bidirectional at the current
concrete-branch stage: from the top-level index one can recover the canonical
empty branch, every pinned single-whole branch, their full-discharge surfaces,
their external final chains, and their public boundaries. -/
def SpectralMeasurePVMOperatorTopologyTopLevelCanonicalProjectionMatrixReady : Prop :=
  SpectralMeasurePVMOperatorTopologyR4ConcreteRouteTopLevelChainIndexReady ∧
  SpectralMeasurePVMOperatorTopologyCanonicalBranchFamilyFinalChainReady ∧
  SpectralMeasurePVMOperatorTopologyCanonicalBranchFamilyFullDischargeReady ∧
  SpectralMeasurePVMOperatorTopologyCanonicalBranchFamilyPublicBoundaryHeld ∧
  SpectralMeasurePVMOperatorTopologyConcreteBranchExternalFinalChainReady
    spectralMeasurePVMConcreteEmptyCountableFamily ∧
  (∀ k : Nat,
    SpectralMeasurePVMOperatorTopologyConcreteBranchExternalFinalChainReady
      (spectralMeasurePVMConcreteSingleWholeAtFamily k)) ∧
  SpectralMeasurePVMOperatorTopologyConcreteBranchFullDischargeReady
    spectralMeasurePVMConcreteEmptyCountableFamily ∧
  (∀ k : Nat,
    SpectralMeasurePVMOperatorTopologyConcreteBranchFullDischargeReady
      (spectralMeasurePVMConcreteSingleWholeAtFamily k)) ∧
  SpectralMeasurePVMOperatorTopologyConcreteBranchExternalFinalReceiptPublicBoundaryHeld
    spectralMeasurePVMConcreteEmptyCountableFamily ∧
  (∀ k : Nat,
    SpectralMeasurePVMOperatorTopologyConcreteBranchExternalFinalReceiptPublicBoundaryHeld
      (spectralMeasurePVMConcreteSingleWholeAtFamily k)) ∧
  SpectralMeasurePVMOperatorTopologyEventualAgreementBatchBridgeReady
    spectralMeasurePVMConcreteEmptyCountableFamily ∧
  (∀ k : Nat,
    SpectralMeasurePVMOperatorTopologyEventualAgreementBatchBridgeReady
      (spectralMeasurePVMConcreteSingleWholeAtFamily k)) ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The top-level canonical projection matrix is ready. -/
theorem spectral_measure_pvm_operator_topology_top_level_canonical_projection_matrix_ready :
    SpectralMeasurePVMOperatorTopologyTopLevelCanonicalProjectionMatrixReady := by
  exact ⟨
    spectral_measure_pvm_operator_topology_r4_concrete_route_top_level_chain_index_ready,
    spectral_measure_pvm_operator_topology_canonical_branch_family_final_chain_ready,
    spectral_measure_pvm_operator_topology_canonical_branch_family_full_discharge_ready,
    spectral_measure_pvm_operator_topology_canonical_branch_family_public_boundary_held,
    spectral_measure_pvm_operator_topology_canonical_empty_family_external_final_chain_ready,
    (by
      intro k
      exact spectral_measure_pvm_operator_topology_canonical_single_whole_family_external_final_chain_ready k),
    spectral_measure_pvm_operator_topology_canonical_empty_family_full_discharge_ready,
    (by
      intro k
      exact spectral_measure_pvm_operator_topology_canonical_single_whole_family_full_discharge_ready k),
    spectral_measure_pvm_operator_topology_canonical_empty_family_external_final_receipt_public_boundary_held,
    (by
      intro k
      exact spectral_measure_pvm_operator_topology_canonical_single_whole_family_external_final_receipt_public_boundary_held k),
    spectral_measure_pvm_operator_topology_canonical_empty_family_eventual_agreement_batch_bridge_ready,
    (by
      intro k
      exact spectral_measure_pvm_operator_topology_canonical_single_whole_family_eventual_agreement_batch_bridge_ready k),
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Projection: the matrix exposes the top-level chain index. -/
theorem spectral_measure_pvm_operator_topology_top_level_canonical_projection_matrix_extracts_chain_index
    (h : SpectralMeasurePVMOperatorTopologyTopLevelCanonicalProjectionMatrixReady) :
    SpectralMeasurePVMOperatorTopologyR4ConcreteRouteTopLevelChainIndexReady := by
  rcases h with ⟨hindex, _, _, _, _, _, _, _, _, _, _, _, _⟩
  exact hindex

/-- Projection: the matrix exposes the canonical branch-family final chain. -/
theorem spectral_measure_pvm_operator_topology_top_level_canonical_projection_matrix_extracts_family_final_chain
    (h : SpectralMeasurePVMOperatorTopologyTopLevelCanonicalProjectionMatrixReady) :
    SpectralMeasurePVMOperatorTopologyCanonicalBranchFamilyFinalChainReady := by
  rcases h with ⟨_, hfamily, _, _, _, _, _, _, _, _, _, _, _⟩
  exact hfamily

/-- Projection: the matrix exposes the canonical branch-family full discharge. -/
theorem spectral_measure_pvm_operator_topology_top_level_canonical_projection_matrix_extracts_family_full_discharge
    (h : SpectralMeasurePVMOperatorTopologyTopLevelCanonicalProjectionMatrixReady) :
    SpectralMeasurePVMOperatorTopologyCanonicalBranchFamilyFullDischargeReady := by
  rcases h with ⟨_, _, hfull, _, _, _, _, _, _, _, _, _, _⟩
  exact hfull

/-- Projection: the matrix exposes the canonical empty external final chain. -/
theorem spectral_measure_pvm_operator_topology_top_level_canonical_projection_matrix_extracts_empty_external_final_chain
    (h : SpectralMeasurePVMOperatorTopologyTopLevelCanonicalProjectionMatrixReady) :
    SpectralMeasurePVMOperatorTopologyConcreteBranchExternalFinalChainReady
      spectralMeasurePVMConcreteEmptyCountableFamily := by
  rcases h with ⟨_, _, _, _, hempty, _, _, _, _, _, _, _, _⟩
  exact hempty

/-- Projection: the matrix exposes every pinned single-whole external final chain. -/
theorem spectral_measure_pvm_operator_topology_top_level_canonical_projection_matrix_extracts_single_whole_external_final_chain
    (h : SpectralMeasurePVMOperatorTopologyTopLevelCanonicalProjectionMatrixReady)
    (k : Nat) :
    SpectralMeasurePVMOperatorTopologyConcreteBranchExternalFinalChainReady
      (spectralMeasurePVMConcreteSingleWholeAtFamily k) := by
  rcases h with ⟨_, _, _, _, _, hsingle, _, _, _, _, _, _, _⟩
  exact hsingle k

/-- Projection: the matrix exposes the canonical empty full discharge. -/
theorem spectral_measure_pvm_operator_topology_top_level_canonical_projection_matrix_extracts_empty_full_discharge
    (h : SpectralMeasurePVMOperatorTopologyTopLevelCanonicalProjectionMatrixReady) :
    SpectralMeasurePVMOperatorTopologyConcreteBranchFullDischargeReady
      spectralMeasurePVMConcreteEmptyCountableFamily := by
  rcases h with ⟨_, _, _, _, _, _, hemptyFull, _, _, _, _, _, _⟩
  exact hemptyFull

/-- Projection: the matrix exposes every pinned single-whole full discharge. -/
theorem spectral_measure_pvm_operator_topology_top_level_canonical_projection_matrix_extracts_single_whole_full_discharge
    (h : SpectralMeasurePVMOperatorTopologyTopLevelCanonicalProjectionMatrixReady)
    (k : Nat) :
    SpectralMeasurePVMOperatorTopologyConcreteBranchFullDischargeReady
      (spectralMeasurePVMConcreteSingleWholeAtFamily k) := by
  rcases h with ⟨_, _, _, _, _, _, _, hsingleFull, _, _, _, _, _⟩
  exact hsingleFull k

/-- Projection: the matrix exposes the canonical empty eventual-agreement batch. -/
theorem spectral_measure_pvm_operator_topology_top_level_canonical_projection_matrix_extracts_empty_eventual_agreement_batch
    (h : SpectralMeasurePVMOperatorTopologyTopLevelCanonicalProjectionMatrixReady) :
    SpectralMeasurePVMOperatorTopologyEventualAgreementBatchBridgeReady
      spectralMeasurePVMConcreteEmptyCountableFamily := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, hemptyBatch, _, _⟩
  exact hemptyBatch

/-- Projection: the matrix exposes every pinned single-whole eventual-agreement
batch. -/
theorem spectral_measure_pvm_operator_topology_top_level_canonical_projection_matrix_extracts_single_whole_eventual_agreement_batch
    (h : SpectralMeasurePVMOperatorTopologyTopLevelCanonicalProjectionMatrixReady)
    (k : Nat) :
    SpectralMeasurePVMOperatorTopologyEventualAgreementBatchBridgeReady
      (spectralMeasurePVMConcreteSingleWholeAtFamily k) := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, hsingleBatch, _⟩
  exact hsingleBatch k

/-- Projection: the matrix preserves no-shell-collapse. -/
theorem spectral_measure_pvm_operator_topology_top_level_canonical_projection_matrix_preserves_no_shell_collapse
    (h : SpectralMeasurePVMOperatorTopologyTopLevelCanonicalProjectionMatrixReady) :
    SpectralMeasurePVMNoShellToFullCollapseBoundary := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hboundary⟩
  exact hboundary

end

end Theorem
end R4
end MGAP4D
