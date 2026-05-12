import MGAP4D.R6.Theorem.IntervalExclusionProofObligationTighteningSeriesReview

namespace MGAP4D
namespace R6
namespace Theorem

structure IntervalExclusionProofObligationTighteningClosure where
  pass1Green : Prop
  pass2Green : Prop
  pass3Green : Prop
  seriesReviewGreen : Prop
  tighteningSegmentClosed : Prop
  r5BridgeClosedAtReviewSurface : Prop
  vacuumSideClosedAtReviewSurface : Prop
  excitedSideClosedAtReviewSurface : Prop
  intervalBoundaryClosedAtReviewSurface : Prop
  intervalExclusionTargetClosedAtReviewSurface : Prop
  mathlibRequestBoundaryClosedAtReviewSurface : Prop
  statusCompatibilityBoundaryClosedAtReviewSurface : Prop
  upstreamR5ReviewSurfaceClosed : Prop
  downstreamR7ReviewSurfaceClosed : Prop
  publicBoundaryClosedAtReviewSurface : Prop
  threeLayerLinksClosedAtReviewSurface : Prop
  r6TheoremRouteStillOpen : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  theoremCompletionNotClaimed : Prop
  downstreamR7NotUnlocked : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def IntervalExclusionProofObligationTighteningClosure.ready
    (C : IntervalExclusionProofObligationTighteningClosure) : Prop :=
  C.pass1Green ∧ C.pass2Green ∧ C.pass3Green ∧ C.seriesReviewGreen ∧
  C.tighteningSegmentClosed ∧ C.r5BridgeClosedAtReviewSurface ∧
  C.vacuumSideClosedAtReviewSurface ∧ C.excitedSideClosedAtReviewSurface ∧
  C.intervalBoundaryClosedAtReviewSurface ∧ C.intervalExclusionTargetClosedAtReviewSurface ∧
  C.mathlibRequestBoundaryClosedAtReviewSurface ∧ C.statusCompatibilityBoundaryClosedAtReviewSurface ∧
  C.upstreamR5ReviewSurfaceClosed ∧ C.downstreamR7ReviewSurfaceClosed ∧
  C.publicBoundaryClosedAtReviewSurface ∧ C.threeLayerLinksClosedAtReviewSurface ∧
  C.r6TheoremRouteStillOpen ∧ C.mainPreMathlib ∧ C.mathlibMainAdoptionHeld ∧
  C.theoremCompletionNotClaimed ∧ C.downstreamR7NotUnlocked ∧
  C.finalGapReleaseNotUnlocked ∧ C.publicBoundaryHeld

theorem interval_exclusion_proof_obligation_tightening_closure_pack
    (C : IntervalExclusionProofObligationTighteningClosure) :
    C.ready ↔ C.pass1Green ∧ C.pass2Green ∧ C.pass3Green ∧ C.seriesReviewGreen ∧
      C.tighteningSegmentClosed ∧ C.r5BridgeClosedAtReviewSurface ∧
      C.vacuumSideClosedAtReviewSurface ∧ C.excitedSideClosedAtReviewSurface ∧
      C.intervalBoundaryClosedAtReviewSurface ∧ C.intervalExclusionTargetClosedAtReviewSurface ∧
      C.mathlibRequestBoundaryClosedAtReviewSurface ∧ C.statusCompatibilityBoundaryClosedAtReviewSurface ∧
      C.upstreamR5ReviewSurfaceClosed ∧ C.downstreamR7ReviewSurfaceClosed ∧
      C.publicBoundaryClosedAtReviewSurface ∧ C.threeLayerLinksClosedAtReviewSurface ∧
      C.r6TheoremRouteStillOpen ∧ C.mainPreMathlib ∧ C.mathlibMainAdoptionHeld ∧
      C.theoremCompletionNotClaimed ∧ C.downstreamR7NotUnlocked ∧
      C.finalGapReleaseNotUnlocked ∧ C.publicBoundaryHeld := by
  rfl

end Theorem
end R6
end MGAP4D
