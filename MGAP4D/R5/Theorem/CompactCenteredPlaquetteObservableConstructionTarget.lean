import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableCandidate

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R5 construction target for the compact centered plaquette observable. -/
def CompactCenteredPlaquetteObservableConstructionTarget : Prop :=
  CompactCenteredPlaquetteObservableR4HandoffInputReady ∧
  Nonempty CompactCenteredPlaquetteObservableCandidate ∧
  MGAP4D.MathlibAnalytic.compactPlaquetteConstructionTheoremReviewSurface.ready ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
    (MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.constructObservable
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette) ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
    (MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.constructObservable
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette) ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
    (MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.constructObservable
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette) ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R5 compact centered plaquette observable construction target is ready. -/
theorem compact_centered_plaquette_observable_construction_target_ready :
    CompactCenteredPlaquetteObservableConstructionTarget := by
  exact ⟨
    compact_centered_plaquette_observable_r4_handoff_input_ready,
    ⟨compactCenteredPlaquetteObservableCandidate⟩,
    MGAP4D.MathlibAnalytic.compact_plaquette_construction_theorem_review_surface_ready,
    compact_centered_plaquette_observable_candidate_compact_support,
    compact_centered_plaquette_observable_candidate_centered,
    compact_centered_plaquette_observable_candidate_smeared,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

/-- R5 construction receipt: the compact centered plaquette observable exists as
an abstract theorem-body object, with later atom/weight stages preserved. -/
def CompactCenteredPlaquetteObservableConstructionReceiptReady : Prop :=
  CompactCenteredPlaquetteObservableConstructionTarget ∧
  Nonempty CompactCenteredPlaquetteObservableCandidate ∧
  CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R5 compact centered plaquette observable construction receipt is ready. -/
theorem compact_centered_plaquette_observable_construction_receipt_ready :
    CompactCenteredPlaquetteObservableConstructionReceiptReady := by
  exact ⟨
    compact_centered_plaquette_observable_construction_target_ready,
    ⟨compactCenteredPlaquetteObservableCandidate⟩,
    compact_centered_plaquette_observable_does_not_consume_atom_3320_boundary,
    compact_centered_plaquette_observable_does_not_consume_positive_spectral_weight_boundary,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R5
end MGAP4D
