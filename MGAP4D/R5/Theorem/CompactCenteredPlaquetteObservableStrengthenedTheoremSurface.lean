import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableStrengthenedTerminalReceipt

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Strengthened theorem surface for R5 compact centered plaquette observable.

This is an R5-only theorem surface: it exposes the strengthened terminal receipt,
the construction certificate, the chosen-observable laws, and the concrete-boundary
ledger without importing R6/R7. -/
def CompactCenteredPlaquetteObservableStrengthenedTheoremSurfaceReady : Prop :=
  CompactCenteredPlaquetteObservableStrengthenedTerminalReceiptReady ∧
  CompactCenteredPlaquetteObservableStrengthenedTerminalReceiptPublicBoundaryHeld ∧
  CompactCenteredPlaquetteObservableConstructionCertificateReady ∧
  CompactCenteredPlaquetteObservableChosenObservableLawsReady ∧
  CompactCenteredPlaquetteObservableAtomChoiceBridgeReady ∧
  CompactCenteredPlaquetteObservableConcreteBoundaryLedgerReady ∧
  CompactCenteredPlaquetteObservableAbstractClosedConcreteBoundaryVisible ∧
  CompactCenteredPlaquetteObservableStrengthenedNoRemainingR5Residual ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The strengthened theorem surface for R5 compact centered plaquette observable is ready. -/
theorem compact_centered_plaquette_observable_strengthened_theorem_surface_ready :
    CompactCenteredPlaquetteObservableStrengthenedTheoremSurfaceReady := by
  exact ⟨
    compact_centered_plaquette_observable_strengthened_terminal_receipt_ready,
    compact_centered_plaquette_observable_strengthened_terminal_receipt_public_boundary_held,
    compact_centered_plaquette_observable_construction_certificate_ready,
    compact_centered_plaquette_observable_chosen_observable_laws_ready,
    compact_centered_plaquette_observable_atom_choice_bridge_ready,
    compact_centered_plaquette_observable_concrete_boundary_ledger_ready,
    compact_centered_plaquette_observable_abstract_closed_concrete_boundary_visible,
    compact_centered_plaquette_observable_strengthened_no_remaining_r5_residual,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary for the strengthened R5 theorem surface. -/
def CompactCenteredPlaquetteObservableStrengthenedTheoremSurfacePublicBoundaryHeld : Prop :=
  CompactCenteredPlaquetteObservableStrengthenedTheoremSurfaceReady ∧
  CompactCenteredPlaquetteObservableStrengthenedTerminalReceiptPublicBoundaryHeld ∧
  CompactCenteredPlaquetteObservableConcreteBoundaryLedgerReady ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary for the strengthened R5 theorem surface is held. -/
theorem compact_centered_plaquette_observable_strengthened_theorem_surface_public_boundary_held :
    CompactCenteredPlaquetteObservableStrengthenedTheoremSurfacePublicBoundaryHeld := by
  exact ⟨
    compact_centered_plaquette_observable_strengthened_theorem_surface_ready,
    compact_centered_plaquette_observable_strengthened_terminal_receipt_public_boundary_held,
    compact_centered_plaquette_observable_concrete_boundary_ledger_ready,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R5
end MGAP4D
