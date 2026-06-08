import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableActualTransportProof

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Actual-proof terminal for R5.

Unlike the earlier receipt-only surfaces, this terminal explicitly includes the
transported proofs that the observable passed into the observable-atom theorem
body is compact, centered, and smeared under the R5 predicates. -/
def CompactCenteredPlaquetteObservableActualProofTerminalReady : Prop :=
  CompactCenteredPlaquetteObservableActualTransportProofReady ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  CompactCenteredPlaquetteObservableStrengthenedFinalExportReceiptReady ∧
  CompactCenteredPlaquetteObservableStrengthenedFinalExportReceiptPublicBoundaryHeld ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual-proof terminal for R5 is ready. -/
theorem compact_centered_plaquette_observable_actual_proof_terminal_ready :
    CompactCenteredPlaquetteObservableActualProofTerminalReady := by
  exact ⟨
    compact_centered_plaquette_observable_actual_transport_proof_ready,
    compact_centered_plaquette_observable_atom_chosen_compact_support,
    compact_centered_plaquette_observable_atom_chosen_centered,
    compact_centered_plaquette_observable_atom_chosen_smeared,
    compact_centered_plaquette_observable_strengthened_final_export_receipt_ready,
    compact_centered_plaquette_observable_strengthened_final_export_receipt_public_boundary_held,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary for the R5 actual-proof terminal. -/
def CompactCenteredPlaquetteObservableActualProofTerminalPublicBoundaryHeld : Prop :=
  CompactCenteredPlaquetteObservableActualProofTerminalReady ∧
  CompactCenteredPlaquetteObservableStrengthenedFinalExportReceiptPublicBoundaryHeld ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary for the R5 actual-proof terminal is held. -/
theorem compact_centered_plaquette_observable_actual_proof_terminal_public_boundary_held :
    CompactCenteredPlaquetteObservableActualProofTerminalPublicBoundaryHeld := by
  exact ⟨
    compact_centered_plaquette_observable_actual_proof_terminal_ready,
    compact_centered_plaquette_observable_strengthened_final_export_receipt_public_boundary_held,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- One-line export theorem: R5 now exposes actual transported compact/centered/
smeared proofs for the atom-chosen observable. -/
theorem compact_centered_plaquette_observable_r5_actual_proof_ready :
    CompactCenteredPlaquetteObservableActualProofTerminalReady := by
  exact compact_centered_plaquette_observable_actual_proof_terminal_ready

end

end Theorem
end R5
end MGAP4D
