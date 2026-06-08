import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableRootFacingEntry

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R5 has no remaining constructive residual for the compact centered plaquette
observable lane: the construction target, receipt, chain index, final receipt,
and root-facing entry are all ready. -/
def CompactCenteredPlaquetteObservableNoRemainingConstructiveResidual : Prop :=
  CompactCenteredPlaquetteObservableConstructionTarget ∧
  CompactCenteredPlaquetteObservableConstructionReceiptReady ∧
  CompactCenteredPlaquetteObservableChainIndexReady ∧
  CompactCenteredPlaquetteObservableFinalReceiptReady ∧
  CompactCenteredPlaquetteObservableRootFacingEntryReady ∧
  Nonempty CompactCenteredPlaquetteObservableCandidate ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- R5 has no remaining constructive residual for the compact centered plaquette
observable lane. -/
theorem compact_centered_plaquette_observable_no_remaining_constructive_residual :
    CompactCenteredPlaquetteObservableNoRemainingConstructiveResidual := by
  exact ⟨
    compact_centered_plaquette_observable_construction_target_ready,
    compact_centered_plaquette_observable_construction_receipt_ready,
    compact_centered_plaquette_observable_chain_index_ready,
    compact_centered_plaquette_observable_final_receipt_ready,
    compact_centered_plaquette_observable_root_facing_entry_ready,
    ⟨compactCenteredPlaquetteObservableCandidate⟩,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Final receipt closing the R5 constructive residual. -/
def CompactCenteredPlaquetteObservableConstructiveResidualClosureFinalReceiptReady : Prop :=
  CompactCenteredPlaquetteObservableNoRemainingConstructiveResidual ∧
  CompactCenteredPlaquetteObservableRootFacingEntryReady ∧
  CompactCenteredPlaquetteObservableRootFacingEntryPublicBoundaryHeld ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The final receipt closing the R5 constructive residual is ready. -/
theorem compact_centered_plaquette_observable_constructive_residual_closure_final_receipt_ready :
    CompactCenteredPlaquetteObservableConstructiveResidualClosureFinalReceiptReady := by
  exact ⟨
    compact_centered_plaquette_observable_no_remaining_constructive_residual,
    compact_centered_plaquette_observable_root_facing_entry_ready,
    compact_centered_plaquette_observable_root_facing_entry_public_boundary_held,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary for R5 constructive residual closure. -/
def CompactCenteredPlaquetteObservableConstructiveResidualClosurePublicBoundaryHeld : Prop :=
  CompactCenteredPlaquetteObservableConstructiveResidualClosureFinalReceiptReady ∧
  CompactCenteredPlaquetteObservableRootFacingEntryPublicBoundaryHeld ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary for R5 constructive residual closure is held. -/
theorem compact_centered_plaquette_observable_constructive_residual_closure_public_boundary_held :
    CompactCenteredPlaquetteObservableConstructiveResidualClosurePublicBoundaryHeld := by
  exact ⟨
    compact_centered_plaquette_observable_constructive_residual_closure_final_receipt_ready,
    compact_centered_plaquette_observable_root_facing_entry_public_boundary_held,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R5
end MGAP4D
