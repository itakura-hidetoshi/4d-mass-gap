import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedOperatorTopologyConcreteBranchR4CompletionHandoff
import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedActualBorelTheoremSurfaceAggregateChainIndex

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- External chain index for the concrete operator-topology branch discharge.

This file sits outside `TheoremSurface`: it imports the already-existing
actual-Borel theorem-surface aggregate chain index and combines it with the new
concrete branch completion handoff.  Thus the concrete branch route becomes
root-facing without introducing a reverse import into `TheoremSurface`. -/
def SpectralMeasurePVMOperatorTopologyConcreteBranchExternalChainIndexReady
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  SpectralMeasurePVMOperatorTopologyConcreteBranchR4CompletionHandoffReady s ∧
  SpectralMeasurePVMOperatorTopologyConcreteBranchFullDischargeReady s ∧
  SpectralMeasurePVMActualBorelTheoremSurfaceAggregateReceiptReady ∧
  SpectralMeasurePVMActualBorelTheoremSurfaceAggregateReceiptPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelTheoremSurfaceAggregateFinalReceiptReady ∧
  SpectralMeasurePVMActualBorelTheoremSurfaceAggregateFinalReceiptPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelTheoremSurfaceAggregateChainIndexReady ∧
  SpectralMeasurePVMActualBorelTheoremSurfaceAggregateChainIndexPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelR4CompletionBoundaryHandoffTarget ∧
  SpectralMeasurePVMOperatorValuedR4CompletionBoundaryHeld ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- A realized concrete branch supplies the external chain index. -/
theorem spectral_measure_pvm_operator_topology_concrete_branch_external_chain_index_ready
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hcase : SpectralMeasurePVMOperatorTopologyBranchRealizationCase s) :
    SpectralMeasurePVMOperatorTopologyConcreteBranchExternalChainIndexReady s := by
  exact ⟨
    spectral_measure_pvm_operator_topology_concrete_branch_r4_completion_handoff_ready s hcase,
    spectral_measure_pvm_operator_topology_concrete_branch_full_discharge_ready s hcase,
    spectral_measure_pvm_actual_borel_theorem_surface_aggregate_receipt_ready,
    spectral_measure_pvm_actual_borel_theorem_surface_aggregate_receipt_public_boundary_held,
    spectral_measure_pvm_actual_borel_theorem_surface_aggregate_final_receipt_ready,
    spectral_measure_pvm_actual_borel_theorem_surface_aggregate_final_receipt_public_boundary_held,
    spectral_measure_pvm_actual_borel_theorem_surface_aggregate_chain_index_ready,
    spectral_measure_pvm_actual_borel_theorem_surface_aggregate_chain_index_public_boundary_held,
    spectral_measure_pvm_actual_borel_r4_completion_boundary_handoff_target_ready,
    spectral_measure_pvm_operator_valued_r4_completion_boundary_held,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The canonical empty family supplies the external chain index. -/
theorem spectral_measure_pvm_operator_topology_canonical_empty_family_external_chain_index_ready :
    SpectralMeasurePVMOperatorTopologyConcreteBranchExternalChainIndexReady
      spectralMeasurePVMConcreteEmptyCountableFamily := by
  exact spectral_measure_pvm_operator_topology_concrete_branch_external_chain_index_ready
    spectralMeasurePVMConcreteEmptyCountableFamily
    spectral_measure_pvm_operator_topology_canonical_empty_family_branch_realization_case

/-- The canonical pinned single-whole family supplies the external chain index at
any pin. -/
theorem spectral_measure_pvm_operator_topology_canonical_single_whole_family_external_chain_index_ready
    (k : Nat) :
    SpectralMeasurePVMOperatorTopologyConcreteBranchExternalChainIndexReady
      (spectralMeasurePVMConcreteSingleWholeAtFamily k) := by
  exact spectral_measure_pvm_operator_topology_concrete_branch_external_chain_index_ready
    (spectralMeasurePVMConcreteSingleWholeAtFamily k)
    (spectral_measure_pvm_operator_topology_canonical_single_whole_family_branch_realization_case k)

/-- Projection: external chain index exposes the concrete branch completion
handoff. -/
theorem spectral_measure_pvm_operator_topology_external_chain_index_extracts_completion_handoff
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyConcreteBranchExternalChainIndexReady s) :
    SpectralMeasurePVMOperatorTopologyConcreteBranchR4CompletionHandoffReady s := by
  rcases h with ⟨hhandoff, _, _, _, _, _, _, _, _, _, _, _⟩
  exact hhandoff

/-- Projection: external chain index exposes the concrete branch full discharge. -/
theorem spectral_measure_pvm_operator_topology_external_chain_index_extracts_full_discharge
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyConcreteBranchExternalChainIndexReady s) :
    SpectralMeasurePVMOperatorTopologyConcreteBranchFullDischargeReady s := by
  rcases h with ⟨_, hfull, _, _, _, _, _, _, _, _, _, _⟩
  exact hfull

/-- Projection: external chain index exposes the actual-Borel aggregate chain
index. -/
theorem spectral_measure_pvm_operator_topology_external_chain_index_extracts_actual_borel_aggregate_chain
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyConcreteBranchExternalChainIndexReady s) :
    SpectralMeasurePVMActualBorelTheoremSurfaceAggregateChainIndexReady := by
  rcases h with ⟨_, _, _, _, _, _, hchain, _, _, _, _, _⟩
  exact hchain

/-- Projection: external chain index exposes the aggregate public boundary. -/
theorem spectral_measure_pvm_operator_topology_external_chain_index_extracts_aggregate_public_boundary
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyConcreteBranchExternalChainIndexReady s) :
    SpectralMeasurePVMActualBorelTheoremSurfaceAggregateChainIndexPublicBoundaryHeld := by
  rcases h with ⟨_, _, _, _, _, _, _, hboundary, _, _, _, _⟩
  exact hboundary

/-- Projection: external chain index keeps the R4 completion boundary held. -/
theorem spectral_measure_pvm_operator_topology_external_chain_index_extracts_r4_completion_held
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyConcreteBranchExternalChainIndexReady s) :
    SpectralMeasurePVMOperatorValuedR4CompletionBoundaryHeld := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, hheld, _, _⟩
  exact hheld

/-- Projection: external chain index keeps the genuine construction open marker. -/
theorem spectral_measure_pvm_operator_topology_external_chain_index_keeps_genuine_construction_open
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyConcreteBranchExternalChainIndexReady s) :
    SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, hopen, _⟩
  exact hopen

/-- Projection: external chain index preserves the no-shell-collapse boundary. -/
theorem spectral_measure_pvm_operator_topology_external_chain_index_preserves_no_shell_collapse
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyConcreteBranchExternalChainIndexReady s) :
    SpectralMeasurePVMNoShellToFullCollapseBoundary := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, hboundary⟩
  exact hboundary

end

end Theorem
end R4
end MGAP4D
