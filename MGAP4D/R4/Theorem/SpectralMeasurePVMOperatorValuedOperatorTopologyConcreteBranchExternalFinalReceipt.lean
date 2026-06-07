import MGAP4D.R4.Theorem.SpectralMeasurePVMOperatorValuedOperatorTopologyConcreteBranchExternalChainIndex

namespace MGAP4D
namespace R4
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- External final receipt for the concrete operator-topology branch route.

This receipt remains outside `TheoremSurface`.  It records that the concrete
branch route has reached the root-facing external chain index while preserving
all open-boundary markers that prevent premature collapse into the still-open
full spectral-measure construction. -/
def SpectralMeasurePVMOperatorTopologyConcreteBranchExternalFinalReceiptReady
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  SpectralMeasurePVMOperatorTopologyConcreteBranchExternalChainIndexReady s ∧
  SpectralMeasurePVMOperatorTopologyConcreteBranchR4CompletionHandoffReady s ∧
  SpectralMeasurePVMOperatorTopologyConcreteBranchFullDischargeReady s ∧
  SpectralMeasurePVMActualBorelTheoremSurfaceAggregateChainIndexReady ∧
  SpectralMeasurePVMActualBorelTheoremSurfaceAggregateChainIndexPublicBoundaryHeld ∧
  SpectralMeasurePVMActualBorelTheoremSurfaceAggregateFinalReceiptReady ∧
  SpectralMeasurePVMActualBorelTheoremSurfaceAggregateFinalReceiptPublicBoundaryHeld ∧
  SpectralMeasurePVMOperatorValuedR4CompletionBoundaryHeld ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- A realized concrete branch supplies the external final receipt. -/
theorem spectral_measure_pvm_operator_topology_concrete_branch_external_final_receipt_ready
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hcase : SpectralMeasurePVMOperatorTopologyBranchRealizationCase s) :
    SpectralMeasurePVMOperatorTopologyConcreteBranchExternalFinalReceiptReady s := by
  exact ⟨
    spectral_measure_pvm_operator_topology_concrete_branch_external_chain_index_ready s hcase,
    spectral_measure_pvm_operator_topology_concrete_branch_r4_completion_handoff_ready s hcase,
    spectral_measure_pvm_operator_topology_concrete_branch_full_discharge_ready s hcase,
    spectral_measure_pvm_actual_borel_theorem_surface_aggregate_chain_index_ready,
    spectral_measure_pvm_actual_borel_theorem_surface_aggregate_chain_index_public_boundary_held,
    spectral_measure_pvm_actual_borel_theorem_surface_aggregate_final_receipt_ready,
    spectral_measure_pvm_actual_borel_theorem_surface_aggregate_final_receipt_public_boundary_held,
    spectral_measure_pvm_operator_valued_r4_completion_boundary_held,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The canonical empty family supplies the external final receipt. -/
theorem spectral_measure_pvm_operator_topology_canonical_empty_family_external_final_receipt_ready :
    SpectralMeasurePVMOperatorTopologyConcreteBranchExternalFinalReceiptReady
      spectralMeasurePVMConcreteEmptyCountableFamily := by
  exact spectral_measure_pvm_operator_topology_concrete_branch_external_final_receipt_ready
    spectralMeasurePVMConcreteEmptyCountableFamily
    spectral_measure_pvm_operator_topology_canonical_empty_family_branch_realization_case

/-- The canonical pinned single-whole family supplies the external final receipt
at any pin. -/
theorem spectral_measure_pvm_operator_topology_canonical_single_whole_family_external_final_receipt_ready
    (k : Nat) :
    SpectralMeasurePVMOperatorTopologyConcreteBranchExternalFinalReceiptReady
      (spectralMeasurePVMConcreteSingleWholeAtFamily k) := by
  exact spectral_measure_pvm_operator_topology_concrete_branch_external_final_receipt_ready
    (spectralMeasurePVMConcreteSingleWholeAtFamily k)
    (spectral_measure_pvm_operator_topology_canonical_single_whole_family_branch_realization_case k)

/-- Public boundary for the concrete branch external final receipt. -/
def SpectralMeasurePVMOperatorTopologyConcreteBranchExternalFinalReceiptPublicBoundaryHeld
    (s : SpectralMeasurePVMConcreteCountableFamily) : Prop :=
  SpectralMeasurePVMOperatorTopologyConcreteBranchExternalFinalReceiptReady s ∧
  SpectralMeasurePVMActualBorelTheoremSurfaceAggregateChainIndexPublicBoundaryHeld ∧
  SpectralMeasurePVMOperatorValuedR4CompletionBoundaryHeld ∧
  SpectralMeasurePVMGenuineSpectralMeasureConstructionStillOpen ∧
  SpectralMeasurePVMR4DoesNotConsumeCompactPlaquetteObservable ∧
  SpectralMeasurePVMOperatorValuedAtom3320DerivationDeferredToLaterStage ∧
  SpectralMeasurePVMOperatorValuedPositiveSpectralWeightDeferredToLaterStage ∧
  SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- A realized concrete branch keeps the public boundary for the external final
receipt. -/
theorem spectral_measure_pvm_operator_topology_concrete_branch_external_final_receipt_public_boundary_held
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (hcase : SpectralMeasurePVMOperatorTopologyBranchRealizationCase s) :
    SpectralMeasurePVMOperatorTopologyConcreteBranchExternalFinalReceiptPublicBoundaryHeld s := by
  exact ⟨
    spectral_measure_pvm_operator_topology_concrete_branch_external_final_receipt_ready s hcase,
    spectral_measure_pvm_actual_borel_theorem_surface_aggregate_chain_index_public_boundary_held,
    spectral_measure_pvm_operator_valued_r4_completion_boundary_held,
    spectral_measure_pvm_genuine_spectral_measure_construction_still_open_ready,
    spectral_measure_pvm_r4_does_not_consume_compact_plaquette_observable_ready,
    spectral_measure_pvm_operator_valued_atom_3320_derivation_deferred_to_later_stage_ready,
    spectral_measure_pvm_operator_valued_positive_spectral_weight_deferred_to_later_stage_ready,
    spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- The canonical empty family keeps the public boundary for the external final
receipt. -/
theorem spectral_measure_pvm_operator_topology_canonical_empty_family_external_final_receipt_public_boundary_held :
    SpectralMeasurePVMOperatorTopologyConcreteBranchExternalFinalReceiptPublicBoundaryHeld
      spectralMeasurePVMConcreteEmptyCountableFamily := by
  exact spectral_measure_pvm_operator_topology_concrete_branch_external_final_receipt_public_boundary_held
    spectralMeasurePVMConcreteEmptyCountableFamily
    spectral_measure_pvm_operator_topology_canonical_empty_family_branch_realization_case

/-- The canonical pinned single-whole family keeps the public boundary for the
external final receipt at any pin. -/
theorem spectral_measure_pvm_operator_topology_canonical_single_whole_family_external_final_receipt_public_boundary_held
    (k : Nat) :
    SpectralMeasurePVMOperatorTopologyConcreteBranchExternalFinalReceiptPublicBoundaryHeld
      (spectralMeasurePVMConcreteSingleWholeAtFamily k) := by
  exact spectral_measure_pvm_operator_topology_concrete_branch_external_final_receipt_public_boundary_held
    (spectralMeasurePVMConcreteSingleWholeAtFamily k)
    (spectral_measure_pvm_operator_topology_canonical_single_whole_family_branch_realization_case k)

/-- Projection: external final receipt exposes the external chain index. -/
theorem spectral_measure_pvm_operator_topology_external_final_receipt_extracts_external_chain_index
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyConcreteBranchExternalFinalReceiptReady s) :
    SpectralMeasurePVMOperatorTopologyConcreteBranchExternalChainIndexReady s := by
  rcases h with ⟨hindex, _, _, _, _, _, _, _, _, _, _, _, _⟩
  exact hindex

/-- Projection: external final receipt exposes the full discharge. -/
theorem spectral_measure_pvm_operator_topology_external_final_receipt_extracts_full_discharge
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyConcreteBranchExternalFinalReceiptReady s) :
    SpectralMeasurePVMOperatorTopologyConcreteBranchFullDischargeReady s := by
  rcases h with ⟨_, _, hfull, _, _, _, _, _, _, _, _, _, _⟩
  exact hfull

/-- Projection: external final receipt preserves the no-shell-collapse boundary. -/
theorem spectral_measure_pvm_operator_topology_external_final_receipt_preserves_no_shell_collapse
    (s : SpectralMeasurePVMConcreteCountableFamily)
    (h : SpectralMeasurePVMOperatorTopologyConcreteBranchExternalFinalReceiptReady s) :
    SpectralMeasurePVMNoShellToFullCollapseBoundary := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hboundary⟩
  exact hboundary

end

end Theorem
end R4
end MGAP4D
