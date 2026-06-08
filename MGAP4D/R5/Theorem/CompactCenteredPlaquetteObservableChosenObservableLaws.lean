import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableCandidate

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- The R5 chosen observable is the observable constructed from the chosen plaquette. -/
theorem compact_centered_plaquette_observable_chosen_observable_is_constructed :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable =
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.constructObservable
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette := by
  exact compact_centered_plaquette_observable_candidate_chosen_observable_def

/-- The R5 chosen observable has compact support. -/
theorem compact_centered_plaquette_observable_chosen_compact_support :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  rw [compact_centered_plaquette_observable_chosen_observable_is_constructed]
  exact compact_centered_plaquette_observable_candidate_compact_support

/-- The R5 chosen observable is centered. -/
theorem compact_centered_plaquette_observable_chosen_centered :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  rw [compact_centered_plaquette_observable_chosen_observable_is_constructed]
  exact compact_centered_plaquette_observable_candidate_centered

/-- The R5 chosen observable is smeared. -/
theorem compact_centered_plaquette_observable_chosen_smeared :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  rw [compact_centered_plaquette_observable_chosen_observable_is_constructed]
  exact compact_centered_plaquette_observable_candidate_smeared

/-- The R5 compact plaquette construction is compatible with the observable atom
choice recorded in the theorem-body layer. -/
theorem compact_centered_plaquette_observable_compatible_with_observable_atom_choice :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compatible_with_observable_atom_choice := by
  exact MGAP4D.MathlibAnalytic.compact_plaquette_compatible_with_observable_atom_choice
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData

/-- The R5 chosen observable agrees with the observable atom theorem body's chosen
observable. -/
theorem compact_centered_plaquette_observable_chosen_eq_observable_atom_chosen :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable =
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable := by
  rfl

/-- Laws package for the chosen R5 observable. -/
def CompactCenteredPlaquetteObservableChosenObservableLawsReady : Prop :=
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable =
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.constructObservable
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compatible_with_observable_atom_choice ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable =
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable

/-- The chosen-observable laws package for R5 is ready. -/
theorem compact_centered_plaquette_observable_chosen_observable_laws_ready :
    CompactCenteredPlaquetteObservableChosenObservableLawsReady := by
  exact ⟨
    compact_centered_plaquette_observable_chosen_observable_is_constructed,
    compact_centered_plaquette_observable_chosen_compact_support,
    compact_centered_plaquette_observable_chosen_centered,
    compact_centered_plaquette_observable_chosen_smeared,
    compact_centered_plaquette_observable_compatible_with_observable_atom_choice,
    compact_centered_plaquette_observable_chosen_eq_observable_atom_chosen⟩

end

end Theorem
end R5
end MGAP4D
