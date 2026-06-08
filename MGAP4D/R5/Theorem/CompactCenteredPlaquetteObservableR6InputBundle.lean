import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableStrengthenedFinalReceipt

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R6 input bundle exported by R5.

This bundle gives R6 a compact, centered, smeared chosen observable, the R5
constructive closure, and the explicit boundary that the 33/20 atom and positive
spectral-weight derivations remain later-stage obligations. -/
def CompactCenteredPlaquetteObservableR6InputBundleReady : Prop :=
  CompactCenteredPlaquetteObservableStrengthenedFinalReceiptReady ∧
  CompactCenteredPlaquetteObservableStrengthenedFinalReceiptPublicBoundaryHeld ∧
  CompactCenteredPlaquetteObservableChosenObservableProofReady ∧
  CompactCenteredPlaquetteObservableLaterStageHandoffFinalReceiptReady ∧
  CompactCenteredPlaquetteObservableR5ConstructiveClosedDownstreamVisible ∧
  Nonempty CompactCenteredPlaquetteObservableCandidate ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R6 input bundle exported by R5 is ready. -/
theorem compact_centered_plaquette_observable_r6_input_bundle_ready :
    CompactCenteredPlaquetteObservableR6InputBundleReady := by
  exact ⟨
    compact_centered_plaquette_observable_strengthened_final_receipt_ready,
    compact_centered_plaquette_observable_strengthened_final_receipt_public_boundary_held,
    compact_centered_plaquette_observable_chosen_observable_proof_ready,
    compact_centered_plaquette_observable_later_stage_handoff_final_receipt_ready,
    compact_centered_plaquette_observable_r5_constructive_closed_downstream_visible,
    ⟨compactCenteredPlaquetteObservableCandidate⟩,
    compact_centered_plaquette_observable_chosen_compact_support,
    compact_centered_plaquette_observable_chosen_centered,
    compact_centered_plaquette_observable_chosen_smeared,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- One-line export theorem for R6. -/
theorem compact_centered_plaquette_observable_export_to_r6_atom_origin :
    CompactCenteredPlaquetteObservableR6InputBundleReady := by
  exact compact_centered_plaquette_observable_r6_input_bundle_ready

end

end Theorem
end R5
end MGAP4D
