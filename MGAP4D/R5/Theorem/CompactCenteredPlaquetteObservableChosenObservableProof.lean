import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableCandidate

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- The R5 chosen plaquette observable has compact support. -/
theorem compact_centered_plaquette_observable_chosen_compact_support :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  rw [compact_centered_plaquette_observable_candidate_chosen_observable_def]
  exact compact_centered_plaquette_observable_candidate_compact_support

/-- The R5 chosen plaquette observable is centered. -/
theorem compact_centered_plaquette_observable_chosen_centered :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  rw [compact_centered_plaquette_observable_candidate_chosen_observable_def]
  exact compact_centered_plaquette_observable_candidate_centered

/-- The R5 chosen plaquette observable is smeared. -/
theorem compact_centered_plaquette_observable_chosen_smeared :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  rw [compact_centered_plaquette_observable_candidate_chosen_observable_def]
  exact compact_centered_plaquette_observable_candidate_smeared

/-- The constructed observable is the chosen observable, in the reverse direction
needed by later handoff stages. -/
theorem compact_centered_plaquette_observable_constructed_eq_chosen :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.constructObservable
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette =
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  exact Eq.symm compact_centered_plaquette_observable_candidate_chosen_observable_def

/-- Proof packet saying the R5 chosen plaquette observable itself is compact,
centered, and smeared. -/
def CompactCenteredPlaquetteObservableChosenObservableProofReady : Prop :=
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.constructObservable
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette =
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
  Nonempty CompactCenteredPlaquetteObservableCandidate ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary

/-- The chosen-observable proof packet is ready. -/
theorem compact_centered_plaquette_observable_chosen_observable_proof_ready :
    CompactCenteredPlaquetteObservableChosenObservableProofReady := by
  exact ⟨
    compact_centered_plaquette_observable_chosen_compact_support,
    compact_centered_plaquette_observable_chosen_centered,
    compact_centered_plaquette_observable_chosen_smeared,
    compact_centered_plaquette_observable_constructed_eq_chosen,
    ⟨compactCenteredPlaquetteObservableCandidate⟩,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary⟩

end

end Theorem
end R5
end MGAP4D
