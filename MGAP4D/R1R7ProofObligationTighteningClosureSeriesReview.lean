import MGAP4D.R1.Theorem.HilbertProofObligationTighteningClosure
import MGAP4D.R2.Theorem.RestrictionProofObligationTighteningClosure
import MGAP4D.R3R7ProofObligationTighteningClosureSeriesReview

namespace MGAP4D

structure R1R7ProofObligationTighteningClosureSeriesReview where
  r1ClosureGreen : Prop
  r2ClosureGreen : Prop
  r3r7ClosureSeriesReviewGreen : Prop
  r1r7ClosureSeriesReviewedAtReviewSurface : Prop
  r1TheoremRouteStillOpen : Prop
  r2TheoremRouteStillOpen : Prop
  r3r7TheoremRoutesStillOpen : Prop
  theoremCompletionsNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  publicBoundaryHeld : Prop

def R1R7ProofObligationTighteningClosureSeriesReview.ready
    (S : R1R7ProofObligationTighteningClosureSeriesReview) : Prop :=
  S.r1ClosureGreen ∧ S.r2ClosureGreen ∧ S.r3r7ClosureSeriesReviewGreen ∧
  S.r1r7ClosureSeriesReviewedAtReviewSurface ∧ S.r1TheoremRouteStillOpen ∧
  S.r2TheoremRouteStillOpen ∧ S.r3r7TheoremRoutesStillOpen ∧
  S.theoremCompletionsNotClaimed ∧ S.finalGapReleaseNotUnlocked ∧
  S.mainPreMathlib ∧ S.mathlibMainAdoptionHeld ∧ S.publicBoundaryHeld

theorem r1_r7_proof_obligation_tightening_closure_series_review_pack
    (S : R1R7ProofObligationTighteningClosureSeriesReview) :
    S.ready ↔ S.r1ClosureGreen ∧ S.r2ClosureGreen ∧ S.r3r7ClosureSeriesReviewGreen ∧
      S.r1r7ClosureSeriesReviewedAtReviewSurface ∧ S.r1TheoremRouteStillOpen ∧
      S.r2TheoremRouteStillOpen ∧ S.r3r7TheoremRoutesStillOpen ∧
      S.theoremCompletionsNotClaimed ∧ S.finalGapReleaseNotUnlocked ∧
      S.mainPreMathlib ∧ S.mathlibMainAdoptionHeld ∧ S.publicBoundaryHeld := by
  rfl

end MGAP4D
