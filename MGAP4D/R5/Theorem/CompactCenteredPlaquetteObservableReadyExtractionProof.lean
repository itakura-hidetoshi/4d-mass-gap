import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableActualProofTerminal

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Extract the singleton compact-plaquette data readiness from the compact
plaquette review surface readiness. -/
theorem compact_centered_plaquette_observable_extract_data_ready_from_review_ready :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.ready := by
  exact MGAP4D.MathlibAnalytic.compact_plaquette_construction_theorem_review_surface_ready.2.1

/-- Extract compact support of the R5 chosen observable from the review-surface
ready package, via the general ready-transport lemma. -/
theorem compact_centered_plaquette_observable_review_ready_chosen_compact_support :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  exact MGAP4D.MathlibAnalytic.compact_plaquette_ready_chosen_compact_support
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData
    compact_centered_plaquette_observable_extract_data_ready_from_review_ready

/-- Extract centeredness of the R5 chosen observable from the review-surface
ready package, via the general ready-transport lemma. -/
theorem compact_centered_plaquette_observable_review_ready_chosen_centered :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  exact MGAP4D.MathlibAnalytic.compact_plaquette_ready_chosen_centered
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData
    compact_centered_plaquette_observable_extract_data_ready_from_review_ready

/-- Extract smearing of the R5 chosen observable from the review-surface ready
package, via the general ready-transport lemma. -/
theorem compact_centered_plaquette_observable_review_ready_chosen_smeared :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  exact MGAP4D.MathlibAnalytic.compact_plaquette_ready_chosen_smeared
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData
    compact_centered_plaquette_observable_extract_data_ready_from_review_ready

/-- Extract all R5 chosen-observable laws from review readiness. -/
theorem compact_centered_plaquette_observable_review_ready_chosen_laws :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  exact ⟨
    compact_centered_plaquette_observable_review_ready_chosen_compact_support,
    compact_centered_plaquette_observable_review_ready_chosen_centered,
    compact_centered_plaquette_observable_review_ready_chosen_smeared⟩

/-- Transport the review-ready laws to the observable-atom chosen observable. -/
theorem compact_centered_plaquette_observable_review_ready_atom_chosen_laws :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable := by
  rw [← compact_centered_plaquette_observable_chosen_eq_observable_atom_chosen]
  exact compact_centered_plaquette_observable_review_ready_chosen_laws

/-- Actual extraction proof package: the properties used downstream are extracted
from review readiness and transported to the atom-chosen observable. -/
def CompactCenteredPlaquetteObservableReadyExtractionProofReady : Prop :=
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.ready ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  CompactCenteredPlaquetteObservableActualProofTerminalReady ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The actual extraction proof package is ready. -/
theorem compact_centered_plaquette_observable_ready_extraction_proof_ready :
    CompactCenteredPlaquetteObservableReadyExtractionProofReady := by
  exact ⟨
    compact_centered_plaquette_observable_extract_data_ready_from_review_ready,
    compact_centered_plaquette_observable_review_ready_atom_chosen_laws.1,
    compact_centered_plaquette_observable_review_ready_atom_chosen_laws.2.1,
    compact_centered_plaquette_observable_review_ready_atom_chosen_laws.2.2,
    compact_centered_plaquette_observable_actual_proof_terminal_ready,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R5
end MGAP4D
