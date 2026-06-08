import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableReviewReadyDirectProof

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Direct-proof final export for R5.

This is the strongest R5 export so far: it includes the direct decomposition of
the review-surface readiness and the transported compact/centered/smeared laws
for the observable-atom chosen observable. -/
def CompactCenteredPlaquetteObservableDirectProofFinalExportReady : Prop :=
  CompactCenteredPlaquetteObservableReviewReadyDirectProofReady ∧
  CompactCenteredPlaquetteObservableActualProofFinalExportReady ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  CompactCenteredPlaquetteObservableStrengthenedFinalExportReceiptReady ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The direct-proof final export for R5 is ready. -/
theorem compact_centered_plaquette_observable_direct_proof_final_export_ready :
    CompactCenteredPlaquetteObservableDirectProofFinalExportReady := by
  exact ⟨
    compact_centered_plaquette_observable_review_ready_direct_proof_ready,
    compact_centered_plaquette_observable_actual_proof_final_export_ready,
    compact_centered_plaquette_observable_review_ready_direct_atom_chosen_laws.1,
    compact_centered_plaquette_observable_review_ready_direct_atom_chosen_laws.2.1,
    compact_centered_plaquette_observable_review_ready_direct_atom_chosen_laws.2.2,
    compact_centered_plaquette_observable_strengthened_final_export_receipt_ready,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary for the direct-proof final export. -/
def CompactCenteredPlaquetteObservableDirectProofFinalExportPublicBoundaryHeld : Prop :=
  CompactCenteredPlaquetteObservableDirectProofFinalExportReady ∧
  CompactCenteredPlaquetteObservableActualProofFinalExportPublicBoundaryHeld ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary for the direct-proof final export is held. -/
theorem compact_centered_plaquette_observable_direct_proof_final_export_public_boundary_held :
    CompactCenteredPlaquetteObservableDirectProofFinalExportPublicBoundaryHeld := by
  exact ⟨
    compact_centered_plaquette_observable_direct_proof_final_export_ready,
    compact_centered_plaquette_observable_actual_proof_final_export_public_boundary_held,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- One-line export theorem: R5 exposes direct-decomposition proof of compact,
centered, and smeared laws for the downstream observable. -/
theorem compact_centered_plaquette_observable_r5_direct_proof_final_export_ready :
    CompactCenteredPlaquetteObservableDirectProofFinalExportReady := by
  exact compact_centered_plaquette_observable_direct_proof_final_export_ready

end

end Theorem
end R5
end MGAP4D
