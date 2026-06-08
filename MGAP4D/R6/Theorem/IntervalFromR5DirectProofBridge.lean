import MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableDirectProofDownstreamInputContract
import MGAP4D.R6.TheoremSurface

namespace MGAP4D
namespace R6
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R6 projection of the R5 direct-proof downstream input: the observable-atom
chosen observable is already compact, centered, and smeared before the R6
interval-exclusion obligations are opened. -/
theorem interval_from_r5_direct_proof_atom_chosen_laws :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable := by
  rcases MGAP4D.R5.Theorem.compact_centered_plaquette_observable_direct_proof_downstream_input_contract_ready with
    ⟨_hfinal, _hpublic, _hchosen, _hchosenCompact, _hchosenCentered, _hchosenSmeared,
      hatomCompact, hatomCentered, hatomSmeared, _hnoAtom, _hnoWeight, _hr4⟩
  exact ⟨hatomCompact, hatomCentered, hatomSmeared⟩

/-- R6 projection of the R5 direct-proof downstream input: the R5 construction
chosen observable is compact, centered, and smeared. -/
theorem interval_from_r5_direct_proof_chosen_laws :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
        MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable := by
  rcases MGAP4D.R5.Theorem.compact_centered_plaquette_observable_direct_proof_downstream_input_contract_ready with
    ⟨_hfinal, _hpublic, _hchosen, hchosenCompact, hchosenCentered, hchosenSmeared,
      _hatomCompact, _hatomCentered, _hatomSmeared, _hnoAtom, _hnoWeight, _hr4⟩
  exact ⟨hchosenCompact, hchosenCentered, hchosenSmeared⟩

/-- R6 bridge-level equality of the R5 chosen observable and the observable-atom
chosen observable, imported through the direct-proof downstream contract. -/
theorem interval_from_r5_direct_proof_chosen_eq_atom_chosen :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable =
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable := by
  rcases MGAP4D.R5.Theorem.compact_centered_plaquette_observable_direct_proof_downstream_input_contract_ready with
    ⟨_hfinal, _hpublic, hchosen, _hchosenCompact, _hchosenCentered, _hchosenSmeared,
      _hatomCompact, _hatomCentered, _hatomSmeared, _hnoAtom, _hnoWeight, _hr4⟩
  exact hchosen

/-- R6 bridge-level preservation of the R5 atom-boundary: R6 interval work has not
consumed the exact 33/20 atom obligation. -/
theorem interval_from_r5_direct_proof_does_not_consume_atom_3320 :
    MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary := by
  rcases MGAP4D.R5.Theorem.compact_centered_plaquette_observable_direct_proof_downstream_input_contract_ready with
    ⟨_hfinal, _hpublic, _hchosen, _hchosenCompact, _hchosenCentered, _hchosenSmeared,
      _hatomCompact, _hatomCentered, _hatomSmeared, hnoAtom, _hnoWeight, _hr4⟩
  exact hnoAtom

/-- R6 bridge-level preservation of the R5 positive-spectral-weight boundary. -/
theorem interval_from_r5_direct_proof_does_not_consume_positive_spectral_weight :
    MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary := by
  rcases MGAP4D.R5.Theorem.compact_centered_plaquette_observable_direct_proof_downstream_input_contract_ready with
    ⟨_hfinal, _hpublic, _hchosen, _hchosenCompact, _hchosenCentered, _hchosenSmeared,
      _hatomCompact, _hatomCentered, _hatomSmeared, _hnoAtom, hnoWeight, _hr4⟩
  exact hnoWeight

/-- R6 bridge-level preservation of the R4 no-shell-to-full-collapse boundary. -/
theorem interval_from_r5_direct_proof_preserves_r4_boundary :
    MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary := by
  rcases MGAP4D.R5.Theorem.compact_centered_plaquette_observable_direct_proof_downstream_input_contract_ready with
    ⟨_hfinal, _hpublic, _hchosen, _hchosenCompact, _hchosenCentered, _hchosenSmeared,
      _hatomCompact, _hatomCentered, _hatomSmeared, _hnoAtom, _hnoWeight, hr4⟩
  exact hr4

/-- R6 bridge package from the R5 direct proof.

This is not a proof of interval exclusion itself.  It is the proof-carrying R5
input that R6 interval-exclusion proofs may consume: both observable faces are
available, the direct-review proof remains upstream, and the atom/weight/R4
boundaries remain visible. -/
def IntervalFromR5DirectProofBridgeReady : Prop :=
  MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableDirectProofDownstreamInputContractReady ∧
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
  MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R6 bridge package from the R5 direct proof is ready. -/
theorem interval_from_r5_direct_proof_bridge_ready :
    IntervalFromR5DirectProofBridgeReady := by
  exact ⟨
    MGAP4D.R5.Theorem.compact_centered_plaquette_observable_direct_proof_downstream_input_contract_ready,
    interval_from_r5_direct_proof_chosen_eq_atom_chosen,
    interval_from_r5_direct_proof_chosen_laws.1,
    interval_from_r5_direct_proof_chosen_laws.2.1,
    interval_from_r5_direct_proof_chosen_laws.2.2,
    interval_from_r5_direct_proof_atom_chosen_laws.1,
    interval_from_r5_direct_proof_atom_chosen_laws.2.1,
    interval_from_r5_direct_proof_atom_chosen_laws.2.2,
    interval_from_r5_direct_proof_does_not_consume_atom_3320,
    interval_from_r5_direct_proof_does_not_consume_positive_spectral_weight,
    interval_from_r5_direct_proof_preserves_r4_boundary⟩

/-- Conditional R6 gap-interval surface constructor.

Given the remaining R6-specific interval/vacuum/excited/exclusion surfaces, the
R5 slot of `GapIntervalSurface` is now filled by the direct R5 proof, rather than
by an opaque readiness receipt. -/
theorem gap_interval_surface_ready_of_r5_direct_proof
    {intervalStatusReady vacuumSideSurface excitedSideSurface exclusionSurface : Prop}
    (hinterval : intervalStatusReady)
    (hvacuum : vacuumSideSurface)
    (hexcited : excitedSideSurface)
    (hexclusion : exclusionSurface) :
    (MGAP4D.R6.TheoremSurface.GapIntervalSurface.mk
      MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableDirectProofDownstreamInputContractReady
      intervalStatusReady
      vacuumSideSurface
      excitedSideSurface
      exclusionSurface).ready := by
  exact ⟨
    MGAP4D.R5.Theorem.compact_centered_plaquette_observable_direct_proof_downstream_input_contract_ready,
    hinterval,
    hvacuum,
    hexcited,
    hexclusion⟩

/-- One-line R6 export: the R5 direct proof is now a proof-carrying R6 interval
bridge input. -/
theorem r6_interval_from_r5_direct_proof_ready :
    IntervalFromR5DirectProofBridgeReady := by
  exact interval_from_r5_direct_proof_bridge_ready

end

end Theorem
end R6
end MGAP4D
