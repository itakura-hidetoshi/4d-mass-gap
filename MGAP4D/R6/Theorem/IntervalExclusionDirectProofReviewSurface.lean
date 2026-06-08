import MGAP4D.R6.Theorem.IntervalExclusionR5DirectProofSlotClosure

namespace MGAP4D
namespace R6
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R6 review surface carrying the direct R5 proof into interval-exclusion work.

This is deliberately not the R6 interval-exclusion theorem itself.  It records
that the upstream R5 slot is closed by the direct proof, that the atom-chosen
observable laws are exposed to R6, and that the direct slot is available for the
closure-candidate, hardening-pass, and tightening-closure constructors. -/
def IntervalExclusionDirectProofReviewSurfaceReady : Prop :=
  IntervalExclusionR5DirectProofSlotClosed ∧
  (MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable) ∧
  (∀ {milestonePresent skeletonBundlePresent intervalSurfaceNamed exclusionBoundaryNamed
        intervalExclusionObligationsVisible downstreamR7AtomExactReviewGated
        mathlibDryRunNotCompletion publicBoundaryHeld : Prop},
      milestonePresent →
      skeletonBundlePresent →
      intervalSurfaceNamed →
      exclusionBoundaryNamed →
      intervalExclusionObligationsVisible →
      downstreamR7AtomExactReviewGated →
      mathlibDryRunNotCompletion →
      publicBoundaryHeld →
      (IntervalExclusionClosureCandidate.mk
        milestonePresent
        skeletonBundlePresent
        intervalSurfaceNamed
        exclusionBoundaryNamed
        intervalExclusionObligationsVisible
        IntervalExclusionR5DirectProofSlotClosed
        downstreamR7AtomExactReviewGated
        mathlibDryRunNotCompletion
        publicBoundaryHeld).ready) ∧
  (∀ {closureCandidateVisible intervalSurfaceVisible exclusionBoundaryVisible
        intervalExclusionObligationsVisible downstreamR7AtomExactReviewGated
        mathlibDryRunNotCompletion theoremCompletionNotClaimed publicBoundaryHeld : Prop},
      closureCandidateVisible →
      intervalSurfaceVisible →
      exclusionBoundaryVisible →
      intervalExclusionObligationsVisible →
      downstreamR7AtomExactReviewGated →
      mathlibDryRunNotCompletion →
      theoremCompletionNotClaimed →
      publicBoundaryHeld →
      (IntervalExclusionHardeningPass.mk
        closureCandidateVisible
        intervalSurfaceVisible
        exclusionBoundaryVisible
        intervalExclusionObligationsVisible
        IntervalExclusionR5DirectProofSlotClosed
        downstreamR7AtomExactReviewGated
        mathlibDryRunNotCompletion
        theoremCompletionNotClaimed
        publicBoundaryHeld).ready) ∧
  (∀ {pass1Green pass2Green pass3Green seriesReviewGreen tighteningSegmentClosed
        vacuumSideClosedAtReviewSurface excitedSideClosedAtReviewSurface
        intervalBoundaryClosedAtReviewSurface intervalExclusionTargetClosedAtReviewSurface
        mathlibRequestBoundaryClosedAtReviewSurface statusCompatibilityBoundaryClosedAtReviewSurface
        downstreamR7ReviewSurfaceClosed publicBoundaryClosedAtReviewSurface
        threeLayerLinksClosedAtReviewSurface r6TheoremRouteStillOpen mainPreMathlib
        mathlibMainAdoptionHeld theoremCompletionNotClaimed downstreamR7NotUnlocked
        finalGapReleaseNotUnlocked publicBoundaryHeld : Prop},
      pass1Green →
      pass2Green →
      pass3Green →
      seriesReviewGreen →
      tighteningSegmentClosed →
      vacuumSideClosedAtReviewSurface →
      excitedSideClosedAtReviewSurface →
      intervalBoundaryClosedAtReviewSurface →
      intervalExclusionTargetClosedAtReviewSurface →
      mathlibRequestBoundaryClosedAtReviewSurface →
      statusCompatibilityBoundaryClosedAtReviewSurface →
      downstreamR7ReviewSurfaceClosed →
      publicBoundaryClosedAtReviewSurface →
      threeLayerLinksClosedAtReviewSurface →
      r6TheoremRouteStillOpen →
      mainPreMathlib →
      mathlibMainAdoptionHeld →
      theoremCompletionNotClaimed →
      downstreamR7NotUnlocked →
      finalGapReleaseNotUnlocked →
      publicBoundaryHeld →
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
        publicBoundaryHeld).ready) ∧
  MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary ∧
  MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary ∧
  MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary

/-- The R6 direct-proof review surface is ready. -/
theorem interval_exclusion_direct_proof_review_surface_ready :
    IntervalExclusionDirectProofReviewSurfaceReady := by
  refine ⟨
    interval_exclusion_r5_direct_proof_slot_closed,
    interval_exclusion_r5_direct_proof_slot_atom_chosen_laws,
    ?_, ?_, ?_,
    interval_from_r5_direct_proof_does_not_consume_atom_3320,
    interval_from_r5_direct_proof_does_not_consume_positive_spectral_weight,
    interval_from_r5_direct_proof_preserves_r4_boundary⟩
  · intro milestonePresent skeletonBundlePresent intervalSurfaceNamed exclusionBoundaryNamed
      intervalExclusionObligationsVisible downstreamR7AtomExactReviewGated
      mathlibDryRunNotCompletion publicBoundaryHeld
      hmilestone hskeleton hintervalSurface hexclusionBoundary hobligations hdownstream hmathlib hpublic
    exact interval_exclusion_closure_candidate_ready_of_r5_direct_proof_slot
      hmilestone hskeleton hintervalSurface hexclusionBoundary hobligations hdownstream hmathlib hpublic
  · intro closureCandidateVisible intervalSurfaceVisible exclusionBoundaryVisible
      intervalExclusionObligationsVisible downstreamR7AtomExactReviewGated
      mathlibDryRunNotCompletion theoremCompletionNotClaimed publicBoundaryHeld
      hclosure hintervalSurface hexclusionBoundary hobligations hdownstream hmathlib hnotComplete hpublic
    exact interval_exclusion_hardening_pass_ready_of_r5_direct_proof_slot
      hclosure hintervalSurface hexclusionBoundary hobligations hdownstream hmathlib hnotComplete hpublic
  · intro pass1Green pass2Green pass3Green seriesReviewGreen tighteningSegmentClosed
      vacuumSideClosedAtReviewSurface excitedSideClosedAtReviewSurface
      intervalBoundaryClosedAtReviewSurface intervalExclusionTargetClosedAtReviewSurface
      mathlibRequestBoundaryClosedAtReviewSurface statusCompatibilityBoundaryClosedAtReviewSurface
      downstreamR7ReviewSurfaceClosed publicBoundaryClosedAtReviewSurface
      threeLayerLinksClosedAtReviewSurface r6TheoremRouteStillOpen mainPreMathlib
      mathlibMainAdoptionHeld theoremCompletionNotClaimed downstreamR7NotUnlocked
      finalGapReleaseNotUnlocked publicBoundaryHeld
      hpass1 hpass2 hpass3 hseries htightening hvacuum hexcited hintervalBoundary
      hexclusionTarget hmathlibRequest hstatus hdownstreamR7 hpublicReview hthreeLayer
      hr6Open hpreMathlib hmathlibHeld hnotComplete hdownstreamLocked hfinalLocked hpublic
    exact interval_exclusion_tightening_closure_ready_of_r5_direct_proof_slot
      hpass1 hpass2 hpass3 hseries htightening hvacuum hexcited hintervalBoundary
      hexclusionTarget hmathlibRequest hstatus hdownstreamR7 hpublicReview hthreeLayer
      hr6Open hpreMathlib hmathlibHeld hnotComplete hdownstreamLocked hfinalLocked hpublic

/-- Projection: R6 has a direct-proof-carrying upstream R5 slot. -/
theorem interval_exclusion_direct_proof_review_surface_r5_slot_closed :
    IntervalExclusionR5DirectProofSlotClosed := by
  exact interval_exclusion_direct_proof_review_surface_ready.1

/-- Projection: R6 exposes the atom-chosen compact/centered/smeared laws from
the direct R5 proof. -/
theorem interval_exclusion_direct_proof_review_surface_atom_chosen_laws :
    MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.compactSupport
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.centered
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable ∧
      MGAP4D.MathlibAnalytic.singletonCompactPlaquetteConstructionTheoremData.smeared
        MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.chosenObservable := by
  exact interval_exclusion_direct_proof_review_surface_ready.2.1

/-- Boundary: R6 direct-proof review does not consume the R7 exact atom. -/
theorem interval_exclusion_direct_proof_review_surface_does_not_consume_atom_3320 :
    MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableDoesNotConsumeAtom3320Boundary := by
  exact interval_exclusion_direct_proof_review_surface_ready.2.2.2.2.1

/-- Boundary: R6 direct-proof review does not consume positive spectral weight. -/
theorem interval_exclusion_direct_proof_review_surface_does_not_consume_positive_weight :
    MGAP4D.R5.Theorem.CompactCenteredPlaquetteObservableDoesNotConsumePositiveSpectralWeightBoundary := by
  exact interval_exclusion_direct_proof_review_surface_ready.2.2.2.2.2.1

/-- Boundary: R6 direct-proof review preserves the R4 no-collapse boundary. -/
theorem interval_exclusion_direct_proof_review_surface_preserves_r4_boundary :
    MGAP4D.R4.Theorem.SpectralMeasurePVMNoShellToFullCollapseBoundary := by
  exact interval_exclusion_direct_proof_review_surface_ready.2.2.2.2.2.2

end

end Theorem
end R6
end MGAP4D
