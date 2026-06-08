import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableStrengthenedRootFacingEntry

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Strengthened handoff from R5 to the exact-atom and positive-weight stages.

This terminal surface says the compact centered smeared R5 observable is not only
constructed, but also identified with the observable-atom theorem body's chosen
observable. -/
def CompactCenteredPlaquetteObservableStrengthenedLaterStageHandoffReady : Prop :=
  CompactCenteredPlaquetteObservableStrengthenedRootFacingEntryReady ∧
  CompactCenteredPlaquetteObservableStrengthenedRootFacingEntryPublicBoundaryHeld ∧
  CompactCenteredPlaquetteObservableLaterStageHandoffFinalReceiptReady ∧
  CompactCenteredPlaquetteObservableAtomChoiceBridgeReady ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable =
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The strengthened R5 handoff to atom and weight stages is ready. -/
theorem compact_centered_plaquette_observable_strengthened_later_stage_handoff_ready :
    CompactCenteredPlaquetteObservableStrengthenedLaterStageHandoffReady := by
  exact ⟨
    compact_centered_plaquette_observable_strengthened_root_facing_entry_ready,
    compact_centered_plaquette_observable_strengthened_root_facing_entry_public_boundary_held,
    compact_centered_plaquette_observable_later_stage_handoff_final_receipt_ready,
    compact_centered_plaquette_observable_atom_choice_bridge_ready,
    compact_centered_plaquette_observable_chosen_eq_observable_atom_chosen,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Final receipt for the strengthened R5 later-stage handoff. -/
def CompactCenteredPlaquetteObservableStrengthenedLaterStageHandoffFinalReceiptReady : Prop :=
  CompactCenteredPlaquetteObservableStrengthenedLaterStageHandoffReady ∧
  CompactCenteredPlaquetteObservableStrengthenedRootFacingEntryReady ∧
  CompactCenteredPlaquetteObservableAtomChoiceBridgePublicBoundaryHeld ∧
  CompactCenteredPlaquetteObservableR5ConstructiveClosedDownstreamVisible ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The final receipt for the strengthened R5 later-stage handoff is ready. -/
theorem compact_centered_plaquette_observable_strengthened_later_stage_handoff_final_receipt_ready :
    CompactCenteredPlaquetteObservableStrengthenedLaterStageHandoffFinalReceiptReady := by
  exact ⟨
    compact_centered_plaquette_observable_strengthened_later_stage_handoff_ready,
    compact_centered_plaquette_observable_strengthened_root_facing_entry_ready,
    compact_centered_plaquette_observable_atom_choice_bridge_public_boundary_held,
    compact_centered_plaquette_observable_r5_constructive_closed_downstream_visible,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- One-line export theorem for R6/R7. -/
theorem compact_centered_plaquette_observable_r5_strengthened_ready_for_r6_r7 :
    CompactCenteredPlaquetteObservableStrengthenedLaterStageHandoffFinalReceiptReady := by
  exact compact_centered_plaquette_observable_strengthened_later_stage_handoff_final_receipt_ready

end

end Theorem
end R5
end MGAP4D
