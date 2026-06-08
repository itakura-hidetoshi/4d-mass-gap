import MGAP4D.R6.Theorem.IntervalFromR5DirectProofBridge
import MGAP4D.R6.Theorem.IntervalExclusionProofObligationTighteningClosure

namespace MGAP4D
namespace R6
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R6 closure of the upstream R5 slot by the direct R5 proof.

This does not claim R6 interval exclusion.  It states only that the R5 input
slot needed by R6 is no longer an opaque receipt: it is filled by the direct
review-ready decomposition exported from R5, with the atom/weight/R4 boundaries
still visible. -/
def IntervalExclusionR5DirectProofSlotClosed : Prop :=
  IntervalFromR5DirectProofBridgeReady ∧
  MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableDirectProofDownstreamInputContractReady ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.chosenObservable =
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
      MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
  MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The upstream R5 slot of R6 is closed by the direct R5 proof. -/
theorem interval_exclusion_r5_direct_proof_slot_closed :
    IntervalExclusionR5DirectProofSlotClosed := by
  exact ⟨
    interval_from_r5_direct_proof_bridge_ready,
    MGAP4D.R5.Theorem.compact_centered_plaquette_observable_direct_proof_downstream_input_contract_ready,
    interval_from_r5_direct_proof_chosen_eq_atom_chosen,
    interval_from_r5_direct_proof_atom_chosen_laws.1,
    interval_from_r5_direct_proof_atom_chosen_laws.2.1,
    interval_from_r5_direct_proof_atom_chosen_laws.2.2,
    interval_from_r5_direct_proof_does_not_consume_atom_3320,
    interval_from_r5_direct_proof_does_not_consume_positive_spectral_weight,
    interval_from_r5_direct_proof_preserves_r4_boundary⟩

/-- Projection: the R6 upstream R5 slot supplies the compact/centered/smeared
atom-chosen observable laws. -/
theorem interval_exclusion_r5_direct_proof_slot_atom_chosen_laws :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable := by
  rcases interval_exclusion_r5_direct_proof_slot_closed with
    ⟨_hbridge, _hcontract, _hchosen, hcompact, hcentered, hsmeared,
      _hnoAtom, _hnoWeight, _hr4⟩
  exact ⟨hcompact, hcentered, hsmeared⟩

/-- Build an R6 closure-candidate readiness package whose upstream R5 slot is
filled by the direct R5 proof. -/
theorem interval_exclusion_closure_candidate_ready_of_r5_direct_proof_slot
    {milestonePresent skeletonBundlePresent intervalSurfaceNamed exclusionBoundaryNamed
      intervalExclusionObligationsVisible downstreamR7AtomExactReviewGated
      mathlibDryRunNotCompletion publicBoundaryHeld : Prop}
    (hmilestone : milestonePresent)
    (hskeleton : skeletonBundlePresent)
    (hintervalSurface : intervalSurfaceNamed)
    (hexclusionBoundary : exclusionBoundaryNamed)
    (hobligations : intervalExclusionObligationsVisible)
    (hdownstream : downstreamR7AtomExactReviewGated)
    (hmathlib : mathlibDryRunNotCompletion)
    (hpublic : publicBoundaryHeld) :
    (IntervalExclusionClosureCandidate.mk
      milestonePresent
      skeletonBundlePresent
      intervalSurfaceNamed
      exclusionBoundaryNamed
      intervalExclusionObligationsVisible
      IntervalExclusionR5DirectProofSlotClosed
      downstreamR7AtomExactReviewGated
      mathlibDryRunNotCompletion
      publicBoundaryHeld).ready := by
  exact ⟨
    hmilestone,
    hskeleton,
    hintervalSurface,
    hexclusionBoundary,
    hobligations,
    interval_exclusion_r5_direct_proof_slot_closed,
    hdownstream,
    hmathlib,
    hpublic⟩

/-- Build an R6 hardening-pass readiness package whose upstream R5 slot is filled
by the direct R5 proof. -/
theorem interval_exclusion_hardening_pass_ready_of_r5_direct_proof_slot
    {closureCandidateVisible intervalSurfaceVisible exclusionBoundaryVisible
      intervalExclusionObligationsVisible downstreamR7AtomExactReviewGated
      mathlibDryRunNotCompletion theoremCompletionNotClaimed publicBoundaryHeld : Prop}
    (hclosure : closureCandidateVisible)
    (hintervalSurface : intervalSurfaceVisible)
    (hexclusionBoundary : exclusionBoundaryVisible)
    (hobligations : intervalExclusionObligationsVisible)
    (hdownstream : downstreamR7AtomExactReviewGated)
    (hmathlib : mathlibDryRunNotCompletion)
    (hnotComplete : theoremCompletionNotClaimed)
    (hpublic : publicBoundaryHeld) :
    (IntervalExclusionHardeningPass.mk
      closureCandidateVisible
      intervalSurfaceVisible
      exclusionBoundaryVisible
      intervalExclusionObligationsVisible
      IntervalExclusionR5DirectProofSlotClosed
      downstreamR7AtomExactReviewGated
      mathlibDryRunNotCompletion
      theoremCompletionNotClaimed
      publicBoundaryHeld).ready := by
  exact ⟨
    hclosure,
    hintervalSurface,
    hexclusionBoundary,
    hobligations,
    interval_exclusion_r5_direct_proof_slot_closed,
    hdownstream,
    hmathlib,
    hnotComplete,
    hpublic⟩

/-- Build the R6 proof-obligation tightening closure with the upstream R5 review
surface closed by the direct R5 proof.

All other R6-specific and downstream fields remain explicit parameters; this
keeps the theorem honest while removing the old ambiguity in the R5 bridge slot. -/
theorem interval_exclusion_tightening_closure_ready_of_r5_direct_proof_slot
    {pass1Green pass2Green pass3Green seriesReviewGreen tighteningSegmentClosed
      vacuumSideClosedAtReviewSurface excitedSideClosedAtReviewSurface
      intervalBoundaryClosedAtReviewSurface intervalExclusionTargetClosedAtReviewSurface
      mathlibRequestBoundaryClosedAtReviewSurface statusCompatibilityBoundaryClosedAtReviewSurface
      downstreamR7ReviewSurfaceClosed publicBoundaryClosedAtReviewSurface
      threeLayerLinksClosedAtReviewSurface r6TheoremRouteStillOpen mainPreMathlib
      mathlibMainAdoptionHeld theoremCompletionNotClaimed downstreamR7NotUnlocked
      finalGapReleaseNotUnlocked publicBoundaryHeld : Prop}
    (hpass1 : pass1Green)
    (hpass2 : pass2Green)
    (hpass3 : pass3Green)
    (hseries : seriesReviewGreen)
    (htightening : tighteningSegmentClosed)
    (hvacuum : vacuumSideClosedAtReviewSurface)
    (hexcited : excitedSideClosedAtReviewSurface)
    (hintervalBoundary : intervalBoundaryClosedAtReviewSurface)
    (hexclusionTarget : intervalExclusionTargetClosedAtReviewSurface)
    (hmathlibRequest : mathlibRequestBoundaryClosedAtReviewSurface)
    (hstatus : statusCompatibilityBoundaryClosedAtReviewSurface)
    (hdownstreamR7 : downstreamR7ReviewSurfaceClosed)
    (hpublicReview : publicBoundaryClosedAtReviewSurface)
    (hthreeLayer : threeLayerLinksClosedAtReviewSurface)
    (hr6Open : r6TheoremRouteStillOpen)
    (hpreMathlib : mainPreMathlib)
    (hmathlibHeld : mathlibMainAdoptionHeld)
    (hnotComplete : theoremCompletionNotClaimed)
    (hdownstreamLocked : downstreamR7NotUnlocked)
    (hfinalLocked : finalGapReleaseNotUnlocked)
    (hpublic : publicBoundaryHeld) :
    (IntervalExclusionProofObligationTighteningClosure.mk
      pass1Green
      pass2Green
      pass3Green
      seriesReviewGreen
      tighteningSegmentClosed
      IntervalExclusionR5DirectProofSlotClosed
      vacuumSideClosedAtReviewSurface
      excitedSideClosedAtReviewSurface
      intervalBoundaryClosedAtReviewSurface
      intervalExclusionTargetClosedAtReviewSurface
      mathlibRequestBoundaryClosedAtReviewSurface
      statusCompatibilityBoundaryClosedAtReviewSurface
      IntervalExclusionR5DirectProofSlotClosed
      downstreamR7ReviewSurfaceClosed
      publicBoundaryClosedAtReviewSurface
      threeLayerLinksClosedAtReviewSurface
      r6TheoremRouteStillOpen
      mainPreMathlib
      mathlibMainAdoptionHeld
      theoremCompletionNotClaimed
      downstreamR7NotUnlocked
      finalGapReleaseNotUnlocked
      publicBoundaryHeld).ready := by
  exact ⟨
    hpass1,
    hpass2,
    hpass3,
    hseries,
    htightening,
    interval_exclusion_r5_direct_proof_slot_closed,
    hvacuum,
    hexcited,
    hintervalBoundary,
    hexclusionTarget,
    hmathlibRequest,
    hstatus,
    interval_exclusion_r5_direct_proof_slot_closed,
    hdownstreamR7,
    hpublicReview,
    hthreeLayer,
    hr6Open,
    hpreMathlib,
    hmathlibHeld,
    hnotComplete,
    hdownstreamLocked,
    hfinalLocked,
    hpublic⟩

/-- One-line export: the R6 interval-exclusion upstream R5 slot is now closed by
the direct R5 proof. -/
theorem r6_interval_exclusion_r5_direct_proof_slot_ready :
    IntervalExclusionR5DirectProofSlotClosed := by
  exact interval_exclusion_r5_direct_proof_slot_closed

end

end Theorem
end R6
end MGAP4D
