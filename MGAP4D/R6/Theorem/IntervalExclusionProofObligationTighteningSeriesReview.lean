import MGAP4D.R6.Theorem.IntervalExclusionProofObligationTighteningPass1
import MGAP4D.R6.Theorem.IntervalExclusionProofObligationTighteningPass2
import MGAP4D.R6.Theorem.IntervalExclusionProofObligationTighteningPass3

namespace MGAP4D
namespace R6
namespace Theorem

structure IntervalExclusionProofObligationTighteningSeriesReview where
  pass1Green : Prop
  pass2Green : Prop
  pass3Green : Prop
  r5BridgeReviewed : Prop
  vacuumSideReviewed : Prop
  excitedSideReviewed : Prop
  intervalBoundaryReviewed : Prop
  intervalExclusionTargetReviewed : Prop
  mathlibRequestBoundaryReviewed : Prop
  statusCompatibilityBoundaryReviewed : Prop
  upstreamR5ReviewSurfaceReviewed : Prop
  downstreamR7ReviewSurfaceReviewed : Prop
  publicBoundaryReviewed : Prop
  threeLayerLinksReviewed : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  theoremCompletionNotClaimed : Prop
  downstreamR7NotUnlocked : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def IntervalExclusionProofObligationTighteningSeriesReview.ready
    (S : IntervalExclusionProofObligationTighteningSeriesReview) : Prop :=
  S.pass1Green ∧ S.pass2Green ∧ S.pass3Green ∧
  S.r5BridgeReviewed ∧ S.vacuumSideReviewed ∧ S.excitedSideReviewed ∧
  S.intervalBoundaryReviewed ∧ S.intervalExclusionTargetReviewed ∧
  S.mathlibRequestBoundaryReviewed ∧ S.statusCompatibilityBoundaryReviewed ∧
  S.upstreamR5ReviewSurfaceReviewed ∧ S.downstreamR7ReviewSurfaceReviewed ∧
  S.publicBoundaryReviewed ∧ S.threeLayerLinksReviewed ∧
  S.mainPreMathlib ∧ S.mathlibMainAdoptionHeld ∧ S.theoremCompletionNotClaimed ∧
  S.downstreamR7NotUnlocked ∧ S.finalGapReleaseNotUnlocked ∧ S.publicBoundaryHeld

theorem interval_exclusion_proof_obligation_tightening_series_review_pack
    (S : IntervalExclusionProofObligationTighteningSeriesReview) :
    S.ready ↔ S.pass1Green ∧ S.pass2Green ∧ S.pass3Green ∧
      S.r5BridgeReviewed ∧ S.vacuumSideReviewed ∧ S.excitedSideReviewed ∧
      S.intervalBoundaryReviewed ∧ S.intervalExclusionTargetReviewed ∧
      S.mathlibRequestBoundaryReviewed ∧ S.statusCompatibilityBoundaryReviewed ∧
      S.upstreamR5ReviewSurfaceReviewed ∧ S.downstreamR7ReviewSurfaceReviewed ∧
      S.publicBoundaryReviewed ∧ S.threeLayerLinksReviewed ∧
      S.mainPreMathlib ∧ S.mathlibMainAdoptionHeld ∧ S.theoremCompletionNotClaimed ∧
      S.downstreamR7NotUnlocked ∧ S.finalGapReleaseNotUnlocked ∧ S.publicBoundaryHeld := by
  rfl

end Theorem
end R6
end MGAP4D
