import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableReadyExtractionProof

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Final actual-proof export for R5 compact centered plaquette observable.

This is stronger than the receipt-only export: downstream stages can import this
file to obtain the extracted compact/centered/smeared proofs for the
observable-atom chosen observable. -/
def CompactCenteredPlaquetteObservableActualProofFinalExportReady : Prop :=
  CompactCenteredPlaquetteObservableReadyExtractionProofReady ∧
  CompactCenteredPlaquetteObservableActualProofTerminalReady ∧
  CompactCenteredPlaquetteObservableStrengthenedFinalExportReceiptReady ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The final actual-proof export for R5 is ready. -/
theorem compact_centered_plaquette_observable_actual_proof_final_export_ready :
    CompactCenteredPlaquetteObservableActualProofFinalExportReady := by
  exact ⟨
    compact_centered_plaquette_observable_ready_extraction_proof_ready,
    compact_centered_plaquette_observable_actual_proof_terminal_ready,
    compact_centered_plaquette_observable_strengthened_final_export_receipt_ready,
    compact_centered_plaquette_observable_review_ready_atom_chosen_laws.1,
    compact_centered_plaquette_observable_review_ready_atom_chosen_laws.2.1,
    compact_centered_plaquette_observable_review_ready_atom_chosen_laws.2.2,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary for the R5 final actual-proof export. -/
def CompactCenteredPlaquetteObservableActualProofFinalExportPublicBoundaryHeld : Prop :=
  CompactCenteredPlaquetteObservableActualProofFinalExportReady ∧
  CompactCenteredPlaquetteObservableActualProofTerminalPublicBoundaryHeld ∧
  CompactCenteredPlaquetteObservableStrengthenedFinalExportReceiptPublicBoundaryHeld ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary for the R5 final actual-proof export is held. -/
theorem compact_centered_plaquette_observable_actual_proof_final_export_public_boundary_held :
    CompactCenteredPlaquetteObservableActualProofFinalExportPublicBoundaryHeld := by
  exact ⟨
    compact_centered_plaquette_observable_actual_proof_final_export_ready,
    compact_centered_plaquette_observable_actual_proof_terminal_public_boundary_held,
    compact_centered_plaquette_observable_strengthened_final_export_receipt_public_boundary_held,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- One-line export theorem: R5 exposes extracted actual compact/centered/smeared
proofs for the downstream observable. -/
theorem compact_centered_plaquette_observable_r5_actual_proof_final_export_ready :
    CompactCenteredPlaquetteObservableActualProofFinalExportReady := by
  exact compact_centered_plaquette_observable_actual_proof_final_export_ready

end

end Theorem
end R5
end MGAP4D
