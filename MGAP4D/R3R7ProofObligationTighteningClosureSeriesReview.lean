import MGAP4D.R3.Theorem.R3ProofObligationTighteningClosure
import MGAP4D.R4.Theorem.LowerBoundProofObligationTighteningClosure
import MGAP4D.R5.Theorem.SpectrumInfimumProofObligationTighteningClosure
import MGAP4D.R6.Theorem.IntervalExclusionProofObligationTighteningClosure
import MGAP4D.R7.Theorem.AtomExactProofObligationTighteningClosure

namespace MGAP4D

structure R3R7ProofObligationTighteningClosureSeriesReview where
  r3ClosureGreen : Prop
  r4ClosureGreen : Prop
  r5ClosureGreen : Prop
  r6ClosureGreen : Prop
  r7ClosureGreen : Prop
  r3RouteReviewed : Prop
  r4RouteReviewed : Prop
  r5RouteReviewed : Prop
  r6RouteReviewed : Prop
  r7RouteReviewed : Prop
  closureSequenceClosedAtReviewSurface : Prop
  theoremRoutesStillOpen : Prop
  theoremCompletionsNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  publicBoundaryHeld : Prop

def R3R7ProofObligationTighteningClosureSeriesReview.ready
    (S : R3R7ProofObligationTighteningClosureSeriesReview) : Prop :=
  S.r3ClosureGreen ∧ S.r4ClosureGreen ∧ S.r5ClosureGreen ∧ S.r6ClosureGreen ∧
  S.r7ClosureGreen ∧ S.r3RouteReviewed ∧ S.r4RouteReviewed ∧ S.r5RouteReviewed ∧
  S.r6RouteReviewed ∧ S.r7RouteReviewed ∧ S.closureSequenceClosedAtReviewSurface ∧
  S.theoremRoutesStillOpen ∧ S.theoremCompletionsNotClaimed ∧
  S.finalGapReleaseNotUnlocked ∧ S.mainPreMathlib ∧ S.mathlibMainAdoptionHeld ∧
  S.publicBoundaryHeld

theorem r3_r7_proof_obligation_tightening_closure_series_review_pack
    (S : R3R7ProofObligationTighteningClosureSeriesReview) :
    S.ready ↔ S.r3ClosureGreen ∧ S.r4ClosureGreen ∧ S.r5ClosureGreen ∧ S.r6ClosureGreen ∧
      S.r7ClosureGreen ∧ S.r3RouteReviewed ∧ S.r4RouteReviewed ∧ S.r5RouteReviewed ∧
      S.r6RouteReviewed ∧ S.r7RouteReviewed ∧ S.closureSequenceClosedAtReviewSurface ∧
      S.theoremRoutesStillOpen ∧ S.theoremCompletionsNotClaimed ∧
      S.finalGapReleaseNotUnlocked ∧ S.mainPreMathlib ∧ S.mathlibMainAdoptionHeld ∧
      S.publicBoundaryHeld := by
  rfl

end MGAP4D
