import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableAtomChoiceBridge
import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableLaterStageHandoff

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Strengthened root-facing entry for R5.

This extends the previous root-facing entry by making explicit that the R5
chosen compact centered smeared observable is the observable-atom theorem body's
chosen observable. -/
def CompactCenteredPlaquetteObservableStrengthenedRootFacingEntryReady : Prop :=
  CompactCenteredPlaquetteObservableRootFacingEntryReady ∧
  CompactCenteredPlaquetteObservableRootFacingEntryPublicBoundaryHeld ∧
  CompactCenteredPlaquetteObservableAtomChoiceBridgeReady ∧
  CompactCenteredPlaquetteObservableAtomChoiceBridgePublicBoundaryHeld ∧
  CompactCenteredPlaquetteObservableChosenObservableLawsReady ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable =
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  CompactCenteredPlaquetteObservableLaterStageHandoffFinalReceiptReady ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The strengthened R5 root-facing entry is ready. -/
theorem compact_centered_plaquette_observable_strengthened_root_facing_entry_ready :
    CompactCenteredPlaquetteObservableStrengthenedRootFacingEntryReady := by
  exact ⟨
    compact_centered_plaquette_observable_root_facing_entry_ready,
    compact_centered_plaquette_observable_root_facing_entry_public_boundary_held,
    compact_centered_plaquette_observable_atom_choice_bridge_ready,
    compact_centered_plaquette_observable_atom_choice_bridge_public_boundary_held,
    compact_centered_plaquette_observable_chosen_observable_laws_ready,
    compact_centered_plaquette_observable_chosen_eq_observable_atom_chosen,
    compact_centered_plaquette_observable_later_stage_handoff_final_receipt_ready,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary for the strengthened R5 root-facing entry. -/
def CompactCenteredPlaquetteObservableStrengthenedRootFacingEntryPublicBoundaryHeld : Prop :=
  CompactCenteredPlaquetteObservableStrengthenedRootFacingEntryReady ∧
  CompactCenteredPlaquetteObservableAtomChoiceBridgePublicBoundaryHeld ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary for the strengthened R5 root-facing entry is held. -/
theorem compact_centered_plaquette_observable_strengthened_root_facing_entry_public_boundary_held :
    CompactCenteredPlaquetteObservableStrengthenedRootFacingEntryPublicBoundaryHeld := by
  exact ⟨
    compact_centered_plaquette_observable_strengthened_root_facing_entry_ready,
    compact_centered_plaquette_observable_atom_choice_bridge_public_boundary_held,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- One-line export theorem: the R5 compact centered plaquette observable is
root-facing and identified with the observable-atom theorem body's chosen
observable. -/
theorem compact_centered_plaquette_observable_r5_strengthened_ready_for_atom_weight_stages :
    CompactCenteredPlaquetteObservableStrengthenedRootFacingEntryReady := by
  exact compact_centered_plaquette_observable_strengthened_root_facing_entry_ready

end

end Theorem
end R5
end MGAP4D
