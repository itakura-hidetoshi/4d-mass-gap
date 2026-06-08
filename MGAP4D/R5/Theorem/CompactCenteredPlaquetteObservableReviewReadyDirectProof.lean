import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableActualProofFinalExport

namespace MGAP4D
namespace R5
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- Directly decompose the compact-plaquette review surface readiness.  This is a
proof-level extraction surface used to avoid treating readiness as an opaque
receipt. -/
theorem compact_centered_plaquette_observable_review_ready_direct_decomposition :
    MGAP4D.MathlibAnalytic.observableAtomTheoremTheoremReviewSurface.ready ∧
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.ready ∧
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
      (MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.constructObservable
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette) ∧
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
      (MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.constructObservable
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette) ∧
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
      (MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.constructObservable
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette) ∧
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable =
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.constructObservable
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenPlaquette := by
  rcases MGAP4D.MathlibAnalytic.compact_plaquette_construction_theorem_review_surface_ready with
    ⟨hatom, hdata, hcompact, hcentered, hsmeared, hchosen, _hbody, _hconcrete, _hfinal, _hpublic⟩
  exact ⟨hatom, hdata, hcompact, hcentered, hsmeared, hchosen⟩

/-- Direct proof from review readiness: the R5 chosen observable has compact
support.  This proof rewrites with the chosen-observable equality extracted from
the review surface itself. -/
theorem compact_centered_plaquette_observable_review_ready_direct_chosen_compact_support :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  rcases compact_centered_plaquette_observable_review_ready_direct_decomposition with
    ⟨_hatom, _hdata, hcompact, _hcentered, _hsmeared, hchosen⟩
  rw [hchosen]
  exact hcompact

/-- Direct proof from review readiness: the R5 chosen observable is centered. -/
theorem compact_centered_plaquette_observable_review_ready_direct_chosen_centered :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  rcases compact_centered_plaquette_observable_review_ready_direct_decomposition with
    ⟨_hatom, _hdata, _hcompact, hcentered, _hsmeared, hchosen⟩
  rw [hchosen]
  exact hcentered

/-- Direct proof from review readiness: the R5 chosen observable is smeared. -/
theorem compact_centered_plaquette_observable_review_ready_direct_chosen_smeared :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  rcases compact_centered_plaquette_observable_review_ready_direct_decomposition with
    ⟨_hatom, _hdata, _hcompact, _hcentered, hsmeared, hchosen⟩
  rw [hchosen]
  exact hsmeared

/-- Direct review-ready proof package for the chosen observable. -/
theorem compact_centered_plaquette_observable_review_ready_direct_chosen_laws :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  exact ⟨
    compact_centered_plaquette_observable_review_ready_direct_chosen_compact_support,
    compact_centered_plaquette_observable_review_ready_direct_chosen_centered,
    compact_centered_plaquette_observable_review_ready_direct_chosen_smeared⟩

/-- Direct review-ready proof transported to the observable-atom chosen observable. -/
theorem compact_centered_plaquette_observable_review_ready_direct_atom_chosen_laws :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable := by
  rw [← compact_centered_plaquette_observable_chosen_eq_observable_atom_chosen]
  exact compact_centered_plaquette_observable_review_ready_direct_chosen_laws

/-- Final direct-proof package: the downstream observable is compact, centered,
and smeared by direct decomposition of R5 review readiness. -/
def CompactCenteredPlaquetteObservableReviewReadyDirectProofReady : Prop :=
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  CompactCenteredPlaquetteObservableActualProofFinalExportReady ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The final direct-proof package is ready. -/
theorem compact_centered_plaquette_observable_review_ready_direct_proof_ready :
    CompactCenteredPlaquetteObservableReviewReadyDirectProofReady := by
  exact ⟨
    compact_centered_plaquette_observable_review_ready_direct_atom_chosen_laws.1,
    compact_centered_plaquette_observable_review_ready_direct_atom_chosen_laws.2.1,
    compact_centered_plaquette_observable_review_ready_direct_atom_chosen_laws.2.2,
    compact_centered_plaquette_observable_actual_proof_final_export_ready,
    MGAP4D.R4.Theorem.spectral_measure_pvm_no_shell_to_full_collapse_boundary_ready⟩

end

end Theorem
end R5
end MGAP4D
