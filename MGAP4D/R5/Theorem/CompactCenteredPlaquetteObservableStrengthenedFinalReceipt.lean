import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableChosenObservableProof
import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableLaterStageHandoff

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Strengthened final receipt for R5: the chosen observable itself, not only the
constructed expression, is proven compact, centered, and smeared. -/
def CompactCenteredPlaquetteObservableStrengthenedFinalReceiptReady : Prop :=
  CompactCenteredPlaquetteObservableFinalReceiptReady ∧
  CompactCenteredPlaquetteObservableRootFacingEntryReady ∧
  CompactCenteredPlaquetteObservableLaterStageHandoffFinalReceiptReady ∧
  CompactCenteredPlaquetteObservableChosenObservableProofReady ∧
  CompactCenteredPlaquetteObservableNoRemainingConstructiveResidual ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The strengthened final receipt for R5 is ready. -/
theorem compact_centered_plaquette_observable_strengthened_final_receipt_ready :
    CompactCenteredPlaquetteObservableStrengthenedFinalReceiptReady := by
  exact ⟨
    compact_centered_plaquette_observable_final_receipt_ready,
    compact_centered_plaquette_observable_root_facing_entry_ready,
    compact_centered_plaquette_observable_later_stage_handoff_final_receipt_ready,
    compact_centered_plaquette_observable_chosen_observable_proof_ready,
    compact_centered_plaquette_observable_no_remaining_constructive_residual,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary for the strengthened R5 final receipt. -/
def CompactCenteredPlaquetteObservableStrengthenedFinalReceiptPublicBoundaryHeld : Prop :=
  CompactCenteredPlaquetteObservableStrengthenedFinalReceiptReady ∧
  CompactCenteredPlaquetteObservableRootFacingEntryPublicBoundaryHeld ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary for the strengthened R5 final receipt is held. -/
theorem compact_centered_plaquette_observable_strengthened_final_receipt_public_boundary_held :
    CompactCenteredPlaquetteObservableStrengthenedFinalReceiptPublicBoundaryHeld := by
  exact ⟨
    compact_centered_plaquette_observable_strengthened_final_receipt_ready,
    compact_centered_plaquette_observable_root_facing_entry_public_boundary_held,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- One-line export theorem: the R5 chosen observable proof is ready for R6 atom
origin derivation. -/
theorem compact_centered_plaquette_observable_chosen_proof_ready_for_r6 :
    CompactCenteredPlaquetteObservableChosenObservableProofReady := by
  exact compact_centered_plaquette_observable_chosen_observable_proof_ready

end

end Theorem
end R5
end MGAP4D
