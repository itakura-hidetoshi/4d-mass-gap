import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableChosenObservableLaws
import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableFinalReceipt

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Bridge from the R5 compact centered plaquette observable to the observable
atom theorem body's chosen observable. -/
def CompactCenteredPlaquetteObservableAtomChoiceBridgeReady : Prop :=
  CompactCenteredPlaquetteObservableFinalReceiptReady ∧
  CompactCenteredPlaquetteObservableFinalReceiptPublicBoundaryHeld ∧
  CompactCenteredPlaquetteObservableChosenObservableLawsReady ∧
  MGAP4D.MathlibAnalytic.observableAtomTheoremTheoremReviewSurface.ready ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable =
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The bridge from the R5 compact centered plaquette observable to the observable
atom theorem body's chosen observable is ready. -/
theorem compact_centered_plaquette_observable_atom_choice_bridge_ready :
    CompactCenteredPlaquetteObservableAtomChoiceBridgeReady := by
  exact ⟨
    compact_centered_plaquette_observable_final_receipt_ready,
    compact_centered_plaquette_observable_final_receipt_public_boundary_held,
    compact_centered_plaquette_observable_chosen_observable_laws_ready,
    MGAP4D.MathlibAnalytic.observable_atom_theorem_theorem_review_surface_ready,
    compact_centered_plaquette_observable_chosen_eq_observable_atom_chosen,
    compact_centered_plaquette_observable_chosen_compact_support,
    compact_centered_plaquette_observable_chosen_centered,
    compact_centered_plaquette_observable_chosen_smeared,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary for the R5 atom-choice bridge. -/
def CompactCenteredPlaquetteObservableAtomChoiceBridgePublicBoundaryHeld : Prop :=
  CompactCenteredPlaquetteObservableAtomChoiceBridgeReady ∧
  CompactCenteredPlaquetteObservableFinalReceiptPublicBoundaryHeld ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary for the R5 atom-choice bridge is held. -/
theorem compact_centered_plaquette_observable_atom_choice_bridge_public_boundary_held :
    CompactCenteredPlaquetteObservableAtomChoiceBridgePublicBoundaryHeld := by
  exact ⟨
    compact_centered_plaquette_observable_atom_choice_bridge_ready,
    compact_centered_plaquette_observable_final_receipt_public_boundary_held,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R5
end MGAP4D
