import MGAP4D.R5.Theorem.SpectrumInfimumProofObligationTighteningPass1
import MGAP4D.R5.Theorem.SpectrumInfimumProofObligationTighteningPass2
import MGAP4D.R5.Theorem.SpectrumInfimumProofObligationTighteningPass3

namespace MGAP4D
namespace R5
namespace Theorem

structure SpectrumInfimumProofObligationTighteningSeriesReview where
  pass1Green : Prop
  pass2Green : Prop
  pass3Green : Prop
  spectrumSetReviewed : Prop
  spectrumBottomReviewed : Prop
  witnessReviewed : Prop
  comparisonReviewed : Prop
  infimumReviewed : Prop
  upstreamR4LowerBoundReviewSurfaceReviewed : Prop
  upstreamR3ZeroFormReviewSurfaceReviewed : Prop
  downstreamR6R7ReviewSurfaceReviewed : Prop
  mathlibRequestBoundaryReviewed : Prop
  publicBoundaryReviewed : Prop
  threeLayerLinksReviewed : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  theoremCompletionNotClaimed : Prop
  downstreamR6R7NotUnlocked : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def SpectrumInfimumProofObligationTighteningSeriesReview.ready
    (S : SpectrumInfimumProofObligationTighteningSeriesReview) : Prop :=
  S.pass1Green ∧ S.pass2Green ∧ S.pass3Green ∧
  S.spectrumSetReviewed ∧ S.spectrumBottomReviewed ∧ S.witnessReviewed ∧
  S.comparisonReviewed ∧ S.infimumReviewed ∧
  S.upstreamR4LowerBoundReviewSurfaceReviewed ∧ S.upstreamR3ZeroFormReviewSurfaceReviewed ∧
  S.downstreamR6R7ReviewSurfaceReviewed ∧ S.mathlibRequestBoundaryReviewed ∧
  S.publicBoundaryReviewed ∧ S.threeLayerLinksReviewed ∧
  S.mainPreMathlib ∧ S.mathlibMainAdoptionHeld ∧ S.theoremCompletionNotClaimed ∧
  S.downstreamR6R7NotUnlocked ∧ S.finalGapReleaseNotUnlocked ∧ S.publicBoundaryHeld

theorem spectrum_infimum_proof_obligation_tightening_series_review_pack
    (S : SpectrumInfimumProofObligationTighteningSeriesReview) :
    S.ready ↔ S.pass1Green ∧ S.pass2Green ∧ S.pass3Green ∧
      S.spectrumSetReviewed ∧ S.spectrumBottomReviewed ∧ S.witnessReviewed ∧
      S.comparisonReviewed ∧ S.infimumReviewed ∧
      S.upstreamR4LowerBoundReviewSurfaceReviewed ∧ S.upstreamR3ZeroFormReviewSurfaceReviewed ∧
      S.downstreamR6R7ReviewSurfaceReviewed ∧ S.mathlibRequestBoundaryReviewed ∧
      S.publicBoundaryReviewed ∧ S.threeLayerLinksReviewed ∧
      S.mainPreMathlib ∧ S.mathlibMainAdoptionHeld ∧ S.theoremCompletionNotClaimed ∧
      S.downstreamR6R7NotUnlocked ∧ S.finalGapReleaseNotUnlocked ∧ S.publicBoundaryHeld := by
  rfl

end Theorem
end R5
end MGAP4D
