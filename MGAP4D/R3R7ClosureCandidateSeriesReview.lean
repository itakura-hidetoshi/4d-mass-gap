import MGAP4D.R3.Theorem.R3ClosureCandidate
import MGAP4D.R4.Theorem.LowerBoundClosureCandidate
import MGAP4D.R5.Theorem.SpectrumInfimumClosureCandidate
import MGAP4D.R6.Theorem.IntervalExclusionClosureCandidate
import MGAP4D.R7.Theorem.AtomExactClosureCandidate

namespace MGAP4D

structure R3R7ClosureCandidateSeriesReview where
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  r3ClosureCandidateGreen : Prop
  r4ClosureCandidateGreen : Prop
  r5ClosureCandidateGreen : Prop
  r6ClosureCandidateGreen : Prop
  r7ClosureCandidateGreen : Prop
  allRoutesVisible : Prop
  allRoutesRemainCandidates : Prop
  theoremCompletionNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def R3R7ClosureCandidateSeriesReview.ready (S : R3R7ClosureCandidateSeriesReview) : Prop :=
  S.mainPreMathlib ∧ S.mathlibMainAdoptionHeld ∧
  S.r3ClosureCandidateGreen ∧ S.r4ClosureCandidateGreen ∧
  S.r5ClosureCandidateGreen ∧ S.r6ClosureCandidateGreen ∧ S.r7ClosureCandidateGreen ∧
  S.allRoutesVisible ∧ S.allRoutesRemainCandidates ∧
  S.theoremCompletionNotClaimed ∧ S.finalGapReleaseNotUnlocked ∧ S.publicBoundaryHeld

theorem r3_r7_closure_candidate_series_review_pack (S : R3R7ClosureCandidateSeriesReview) :
    S.ready ↔ S.mainPreMathlib ∧ S.mathlibMainAdoptionHeld ∧
      S.r3ClosureCandidateGreen ∧ S.r4ClosureCandidateGreen ∧
      S.r5ClosureCandidateGreen ∧ S.r6ClosureCandidateGreen ∧ S.r7ClosureCandidateGreen ∧
      S.allRoutesVisible ∧ S.allRoutesRemainCandidates ∧
      S.theoremCompletionNotClaimed ∧ S.finalGapReleaseNotUnlocked ∧ S.publicBoundaryHeld := by
  rfl

end MGAP4D
