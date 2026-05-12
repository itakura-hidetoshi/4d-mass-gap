import MGAP4D.R5.Theorem.SpectrumInfimumProofObligationTighteningSeriesReview

namespace MGAP4D
namespace R5
namespace Theorem

structure SpectrumInfimumProofObligationTighteningClosure where
  pass1Green : Prop
  pass2Green : Prop
  pass3Green : Prop
  seriesReviewGreen : Prop
  tighteningSegmentClosed : Prop
  spectrumSetClosedAtReviewSurface : Prop
  spectrumBottomClosedAtReviewSurface : Prop
  witnessClosedAtReviewSurface : Prop
  comparisonClosedAtReviewSurface : Prop
  infimumClosedAtReviewSurface : Prop
  upstreamR4LowerBoundReviewSurfaceClosed : Prop
  upstreamR3ZeroFormReviewSurfaceClosed : Prop
  downstreamR6R7ReviewSurfaceClosed : Prop
  mathlibRequestBoundaryClosedAtReviewSurface : Prop
  publicBoundaryClosedAtReviewSurface : Prop
  threeLayerLinksClosedAtReviewSurface : Prop
  r5TheoremRouteStillOpen : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  theoremCompletionNotClaimed : Prop
  downstreamR6R7NotUnlocked : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def SpectrumInfimumProofObligationTighteningClosure.ready
    (C : SpectrumInfimumProofObligationTighteningClosure) : Prop :=
  C.pass1Green ∧ C.pass2Green ∧ C.pass3Green ∧ C.seriesReviewGreen ∧
  C.tighteningSegmentClosed ∧ C.spectrumSetClosedAtReviewSurface ∧
  C.spectrumBottomClosedAtReviewSurface ∧ C.witnessClosedAtReviewSurface ∧
  C.comparisonClosedAtReviewSurface ∧ C.infimumClosedAtReviewSurface ∧
  C.upstreamR4LowerBoundReviewSurfaceClosed ∧ C.upstreamR3ZeroFormReviewSurfaceClosed ∧
  C.downstreamR6R7ReviewSurfaceClosed ∧ C.mathlibRequestBoundaryClosedAtReviewSurface ∧
  C.publicBoundaryClosedAtReviewSurface ∧ C.threeLayerLinksClosedAtReviewSurface ∧
  C.r5TheoremRouteStillOpen ∧ C.mainPreMathlib ∧ C.mathlibMainAdoptionHeld ∧
  C.theoremCompletionNotClaimed ∧ C.downstreamR6R7NotUnlocked ∧
  C.finalGapReleaseNotUnlocked ∧ C.publicBoundaryHeld

theorem spectrum_infimum_proof_obligation_tightening_closure_pack
    (C : SpectrumInfimumProofObligationTighteningClosure) :
    C.ready ↔ C.pass1Green ∧ C.pass2Green ∧ C.pass3Green ∧ C.seriesReviewGreen ∧
      C.tighteningSegmentClosed ∧ C.spectrumSetClosedAtReviewSurface ∧
      C.spectrumBottomClosedAtReviewSurface ∧ C.witnessClosedAtReviewSurface ∧
      C.comparisonClosedAtReviewSurface ∧ C.infimumClosedAtReviewSurface ∧
      C.upstreamR4LowerBoundReviewSurfaceClosed ∧ C.upstreamR3ZeroFormReviewSurfaceClosed ∧
      C.downstreamR6R7ReviewSurfaceClosed ∧ C.mathlibRequestBoundaryClosedAtReviewSurface ∧
      C.publicBoundaryClosedAtReviewSurface ∧ C.threeLayerLinksClosedAtReviewSurface ∧
      C.r5TheoremRouteStillOpen ∧ C.mainPreMathlib ∧ C.mathlibMainAdoptionHeld ∧
      C.theoremCompletionNotClaimed ∧ C.downstreamR6R7NotUnlocked ∧
      C.finalGapReleaseNotUnlocked ∧ C.publicBoundaryHeld := by
  rfl

end Theorem
end R5
end MGAP4D
