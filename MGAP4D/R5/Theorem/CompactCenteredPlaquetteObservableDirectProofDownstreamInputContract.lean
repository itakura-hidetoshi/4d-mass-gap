import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableDirectProofFinalExport

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Projection of the direct-proof final export to the observable-atom chosen
observable laws.  This is intentionally only a projection theorem: the actual
proof work is the direct `rcases` decomposition of the review-ready surface in
`CompactCenteredPlaquetteObservableReviewReadyDirectProof`. -/
theorem compact_centered_plaquette_observable_direct_final_export_atom_chosen_laws :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable := by
  rcases compact_centered_plaquette_observable_direct_proof_final_export_ready with
    ⟨_hdirect, _hactual, hcompact, hcentered, hsmeared,
      _hstrengthened, _hnoAtom, _hnoWeight, _hr4⟩
  exact ⟨hcompact, hcentered, hsmeared⟩

/-- Direct-final-export projection: compact support for the observable-atom
chosen observable. -/
theorem compact_centered_plaquette_observable_direct_final_export_atom_chosen_compact_support :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable := by
  exact compact_centered_plaquette_observable_direct_final_export_atom_chosen_laws.1

/-- Direct-final-export projection: centeredness for the observable-atom chosen
observable. -/
theorem compact_centered_plaquette_observable_direct_final_export_atom_chosen_centered :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable := by
  exact compact_centered_plaquette_observable_direct_final_export_atom_chosen_laws.2.1

/-- Direct-final-export projection: smearing for the observable-atom chosen
observable. -/
theorem compact_centered_plaquette_observable_direct_final_export_atom_chosen_smeared :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable := by
  exact compact_centered_plaquette_observable_direct_final_export_atom_chosen_laws.2.2

/-- Transport the direct-final-export atom laws back across the R5 chosen-observable
identification.  This gives downstream stages either face of the same chosen
observable without reopening the review-ready proof. -/
theorem compact_centered_plaquette_observable_direct_final_export_chosen_laws :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  rw [compact_centered_plaquette_observable_chosen_eq_observable_atom_chosen]
  exact compact_centered_plaquette_observable_direct_final_export_atom_chosen_laws

/-- Direct-final-export projection: compact support for the R5 chosen observable. -/
theorem compact_centered_plaquette_observable_direct_final_export_chosen_compact_support :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  exact compact_centered_plaquette_observable_direct_final_export_chosen_laws.1

/-- Direct-final-export projection: centeredness for the R5 chosen observable. -/
theorem compact_centered_plaquette_observable_direct_final_export_chosen_centered :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  exact compact_centered_plaquette_observable_direct_final_export_chosen_laws.2.1

/-- Direct-final-export projection: smearing for the R5 chosen observable. -/
theorem compact_centered_plaquette_observable_direct_final_export_chosen_smeared :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  exact compact_centered_plaquette_observable_direct_final_export_chosen_laws.2.2

/-- R5 direct-proof downstream input contract.

This is the bridge-shaped form that R6/R7 should consume: it keeps the direct
review-ready decomposition as the upstream certificate, exposes both chosen
observable faces, and preserves the later-stage atom/weight boundaries. -/
def CompactCenteredPlaquetteObservableDirectProofDownstreamInputContractReady : Prop :=
  CompactCenteredPlaquetteObservableDirectProofFinalExportReady ∧
  CompactCenteredPlaquetteObservableDirectProofFinalExportPublicBoundaryHeld ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable =
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R5 direct-proof downstream input contract is ready. -/
theorem compact_centered_plaquette_observable_direct_proof_downstream_input_contract_ready :
    CompactCenteredPlaquetteObservableDirectProofDownstreamInputContractReady := by
  exact ⟨
    compact_centered_plaquette_observable_direct_proof_final_export_ready,
    compact_centered_plaquette_observable_direct_proof_final_export_public_boundary_held,
    compact_centered_plaquette_observable_chosen_eq_observable_atom_chosen,
    compact_centered_plaquette_observable_direct_final_export_chosen_compact_support,
    compact_centered_plaquette_observable_direct_final_export_chosen_centered,
    compact_centered_plaquette_observable_direct_final_export_chosen_smeared,
    compact_centered_plaquette_observable_direct_final_export_atom_chosen_compact_support,
    compact_centered_plaquette_observable_direct_final_export_atom_chosen_centered,
    compact_centered_plaquette_observable_direct_final_export_atom_chosen_smeared,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- Public boundary for the R5 direct-proof downstream input contract. -/
def CompactCenteredPlaquetteObservableDirectProofDownstreamInputContractPublicBoundaryHeld : Prop :=
  CompactCenteredPlaquetteObservableDirectProofDownstreamInputContractReady ∧
  CompactCenteredPlaquetteObservableDirectProofFinalExportPublicBoundaryHeld ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The public boundary for the R5 direct-proof downstream input contract is held. -/
theorem compact_centered_plaquette_observable_direct_proof_downstream_input_contract_public_boundary_held :
    CompactCenteredPlaquetteObservableDirectProofDownstreamInputContractPublicBoundaryHeld := by
  exact ⟨
    compact_centered_plaquette_observable_direct_proof_downstream_input_contract_ready,
    compact_centered_plaquette_observable_direct_proof_final_export_public_boundary_held,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- One-line export theorem for downstream stages. -/
theorem compact_centered_plaquette_observable_r5_direct_proof_downstream_input_ready :
    CompactCenteredPlaquetteObservableDirectProofDownstreamInputContractReady := by
  exact compact_centered_plaquette_observable_direct_proof_downstream_input_contract_ready

end

end Theorem
end R5
end MGAP4D
