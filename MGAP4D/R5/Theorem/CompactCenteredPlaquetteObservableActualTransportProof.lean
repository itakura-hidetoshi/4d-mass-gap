import MGAP4D.MathlibAnalytic.CompactPlaquetteChosenObservableLemmas
import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableStrengthenedFinalExportReceipt

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R5 actual proof: the singleton chosen observable has compact support, derived
by transport from the constructed observable, not merely by a receipt field. -/
theorem compact_centered_plaquette_observable_actual_chosen_compact_support :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  exact MGAP4D.MathlibAnalytic.singleton_compact_plaquette_chosen_compact_support

/-- R5 actual proof: the singleton chosen observable is centered, derived by
transport from the constructed observable. -/
theorem compact_centered_plaquette_observable_actual_chosen_centered :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  exact MGAP4D.MathlibAnalytic.singleton_compact_plaquette_chosen_centered

/-- R5 actual proof: the singleton chosen observable is smeared, derived by
transport from the constructed observable. -/
theorem compact_centered_plaquette_observable_actual_chosen_smeared :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  exact MGAP4D.MathlibAnalytic.singleton_compact_plaquette_chosen_smeared

/-- R5 actual proof: the observable-atom chosen observable has compact support
under the R5 compact plaquette construction predicate. -/
theorem compact_centered_plaquette_observable_atom_chosen_compact_support :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable := by
  rw [← compact_centered_plaquette_observable_chosen_eq_observable_atom_chosen]
  exact compact_centered_plaquette_observable_actual_chosen_compact_support

/-- R5 actual proof: the observable-atom chosen observable is centered under the
R5 compact plaquette construction predicate. -/
theorem compact_centered_plaquette_observable_atom_chosen_centered :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable := by
  rw [← compact_centered_plaquette_observable_chosen_eq_observable_atom_chosen]
  exact compact_centered_plaquette_observable_actual_chosen_centered

/-- R5 actual proof: the observable-atom chosen observable is smeared under the
R5 compact plaquette construction predicate. -/
theorem compact_centered_plaquette_observable_atom_chosen_smeared :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable := by
  rw [← compact_centered_plaquette_observable_chosen_eq_observable_atom_chosen]
  exact compact_centered_plaquette_observable_actual_chosen_smeared

/-- Actual R5 theorem package: the same observable passed to the atom theorem body
is compact, centered, and smeared. -/
theorem compact_centered_plaquette_observable_actual_atom_chosen_laws :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable := by
  exact ⟨
    compact_centered_plaquette_observable_atom_chosen_compact_support,
    compact_centered_plaquette_observable_atom_chosen_centered,
    compact_centered_plaquette_observable_atom_chosen_smeared⟩

/-- Strengthened actual-transport proof surface for R5. -/
def CompactCenteredPlaquetteObservableActualTransportProofReady : Prop :=
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  CompactCenteredPlaquetteObservableStrengthenedFinalExportReceiptReady ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The strengthened actual-transport proof surface for R5 is ready. -/
theorem compact_centered_plaquette_observable_actual_transport_proof_ready :
    CompactCenteredPlaquetteObservableActualTransportProofReady := by
  exact ⟨
    compact_centered_plaquette_observable_atom_chosen_compact_support,
    compact_centered_plaquette_observable_atom_chosen_centered,
    compact_centered_plaquette_observable_atom_chosen_smeared,
    compact_centered_plaquette_observable_strengthened_final_export_receipt_ready,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R5
end MGAP4D
