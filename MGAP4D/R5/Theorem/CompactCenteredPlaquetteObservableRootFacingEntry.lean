import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableFinalReceipt

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Root-facing entry for R5 compact centered plaquette observable construction.

This is the R5 terminal surface intended for R6/R7 handoff.  It asserts the
compact centered plaquette observable construction lane is ready, while keeping
33/20 atom derivation and positive spectral-weight derivation deferred. -/
def CompactCenteredPlaquetteObservableRootFacingEntryReady : Prop :=
  CompactCenteredPlaquetteObservableFinalReceiptReady ∧
  CompactCenteredPlaquetteObservableFinalReceiptPublicBoundaryHeld ∧
  CompactCenteredPlaquetteObservableChainIndexReady ∧
  CompactCenteredPlaquetteObservableConstructionReceiptReady ∧
  Nonempty CompactCenteredPlaquetteObservableCandidate ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The root-facing entry for R5 compact centered plaquette observable construction
is ready. -/
theorem compact_centered_plaquette_observable_root_facing_entry_ready :
    CompactCenteredPlaquetteObservableRootFacingEntryReady := by
  exact ⟨
    compact_centered_plaquette_observable_final_receipt_ready,
    compact_centered_plaquette_observable_final_receipt_public_boundary_held,
    compact_centered_plaquette_observable_chain_index_ready,
    compact_centered_plaquette_observable_construction_receipt_ready,
    ⟨compactCenteredPlaquetteObservableCandidate⟩,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary for the R5 root-facing entry. -/
def CompactCenteredPlaquetteObservableRootFacingEntryPublicBoundaryHeld : Prop :=
  CompactCenteredPlaquetteObservableRootFacingEntryReady ∧
  CompactCenteredPlaquetteObservableFinalReceiptPublicBoundaryHeld ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary for the R5 root-facing entry is held. -/
theorem compact_centered_plaquette_observable_root_facing_entry_public_boundary_held :
    CompactCenteredPlaquetteObservableRootFacingEntryPublicBoundaryHeld := by
  exact ⟨
    compact_centered_plaquette_observable_root_facing_entry_ready,
    compact_centered_plaquette_observable_final_receipt_public_boundary_held,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- One-line export theorem: R5 compact centered plaquette observable construction
is ready for later atom/weight stages. -/
theorem compact_centered_plaquette_observable_r5_ready_for_later_atom_weight_stages :
    CompactCenteredPlaquetteObservableRootFacingEntryReady := by
  exact compact_centered_plaquette_observable_root_facing_entry_ready

end

end Theorem
end R5
end MGAP4D
