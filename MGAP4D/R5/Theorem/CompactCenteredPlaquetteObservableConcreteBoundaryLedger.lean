import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableConstructionCertificate

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Boundary ledger for R5.

The abstract compact centered smeared plaquette observable construction is
certified.  The concrete lattice-gauge plaquette realization is deliberately
kept visible as a boundary rather than silently collapsed into the abstract
prototype. -/
def CompactCenteredPlaquetteObservableConcreteBoundaryLedgerReady : Prop :=
  CompactCenteredPlaquetteObservableConstructionCertificateReady ∧
  CompactCenteredPlaquetteObservableStrengthenedLaterStageHandoffFinalReceiptReady ∧
  CompactCenteredPlaquetteObservableChosenObservableLawsReady ∧
  CompactCenteredPlaquetteObservableAtomChoiceBridgeReady ∧
  MGAP4D.MathlibAnalytic.CompactPlaquetteConstructionTheoremReviewSurface.concreteLatticeGaugePlaquetteStillOpen
    MGAP4D.MathlibAnalytic.compactPlaquetteConstructionTheoremReviewSurface ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R5 concrete boundary ledger is ready. -/
theorem compact_centered_plaquette_observable_concrete_boundary_ledger_ready :
    CompactCenteredPlaquetteObservableConcreteBoundaryLedgerReady := by
  exact ⟨
    compact_centered_plaquette_observable_construction_certificate_ready,
    compact_centered_plaquette_observable_strengthened_later_stage_handoff_final_receipt_ready,
    compact_centered_plaquette_observable_chosen_observable_laws_ready,
    compact_centered_plaquette_observable_atom_choice_bridge_ready,
    compact_centered_plaquette_observable_concrete_lattice_gauge_boundary_still_open,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R5 abstract construction is closed while the concrete lattice-gauge boundary
remains explicit. -/
def CompactCenteredPlaquetteObservableAbstractClosedConcreteBoundaryVisible : Prop :=
  CompactCenteredPlaquetteObservableR5ConstructiveClosedDownstreamVisible ∧
  CompactCenteredPlaquetteObservableConcreteBoundaryLedgerReady ∧
  MGAP4D.MathlibAnalytic.CompactPlaquetteConstructionTheoremReviewSurface.concreteLatticeGaugePlaquetteStillOpen
    MGAP4D.MathlibAnalytic.compactPlaquetteConstructionTheoremReviewSurface ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- R5 abstract construction is closed while the concrete lattice-gauge boundary
remains explicit. -/
theorem compact_centered_plaquette_observable_abstract_closed_concrete_boundary_visible :
    CompactCenteredPlaquetteObservableAbstractClosedConcreteBoundaryVisible := by
  exact ⟨
    compact_centered_plaquette_observable_r5_constructive_closed_downstream_visible,
    compact_centered_plaquette_observable_concrete_boundary_ledger_ready,
    compact_centered_plaquette_observable_concrete_lattice_gauge_boundary_still_open,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R5
end MGAP4D
