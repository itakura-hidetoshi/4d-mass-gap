import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableR4Handoff

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R5 compact centered plaquette observable candidate, backed by the existing
abstract CompactPlaquetteConstructionTheorem review surface. -/
structure CompactCenteredPlaquetteObservableCandidate where
  input_ready : CompactCenteredPlaquetteObservableR4HandoffInputReady
  construction_data_ready :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.ready
  construction_review_ready :
    MGAP4D.MathlibAnalytic.compactPlaquetteConstructionTheoremReviewSurface.ready
  compact_support :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
      (MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.constructObservable
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette)
  centered :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
      (MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.constructObservable
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette)
  smeared :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
      (MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.constructObservable
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette)
  chosen_observable_def :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable =
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.constructObservable
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette
  does_not_consume_atom_3320 : CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary
  does_not_consume_positive_weight : CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary

/-- The canonical R5 compact centered plaquette observable candidate. -/
def compactCenteredPlaquetteObservableCandidate : CompactCenteredPlaquetteObservableCandidate where
  input_ready := compact_centered_plaquette_observable_r4_handoff_input_ready
  construction_data_ready :=
    MGAP4D.MathlibAnalytic.singleton_compact_plaquette_construction_theorem_data_ready
  construction_review_ready :=
    MGAP4D.MathlibAnalytic.compact_plaquette_construction_theorem_review_surface_ready
  compact_support :=
    MGAP4D.MathlibAnalytic.singleton_compact_plaquette_constructed_compact_support
  centered :=
    MGAP4D.MathlibAnalytic.singleton_compact_plaquette_constructed_centered
  smeared :=
    MGAP4D.MathlibAnalytic.singleton_compact_plaquette_constructed_smeared
  chosen_observable_def :=
    MGAP4D.MathlibAnalytic.singleton_compact_plaquette_chosen_observable_def
  does_not_consume_atom_3320 :=
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary
  does_not_consume_positive_weight :=
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary

/-- The canonical R5 candidate has compact support. -/
theorem compact_centered_plaquette_observable_candidate_compact_support :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
      (MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.constructObservable
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette) := by
  exact compactCenteredPlaquetteObservableCandidate.compact_support

/-- The canonical R5 candidate is centered. -/
theorem compact_centered_plaquette_observable_candidate_centered :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
      (MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.constructObservable
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette) := by
  exact compactCenteredPlaquetteObservableCandidate.centered

/-- The canonical R5 candidate is smeared. -/
theorem compact_centered_plaquette_observable_candidate_smeared :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
      (MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.constructObservable
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette) := by
  exact compactCenteredPlaquetteObservableCandidate.smeared

/-- The canonical R5 candidate is definitionally the chosen observable constructed
from the chosen plaquette. -/
theorem compact_centered_plaquette_observable_candidate_chosen_observable_def :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable =
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.constructObservable
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette := by
  exact compactCenteredPlaquetteObservableCandidate.chosen_observable_def

end

end Theorem
end R5
end MGAP4D
