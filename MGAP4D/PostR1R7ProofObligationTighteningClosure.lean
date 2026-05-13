import MGAP4D.R1R7ProofObligationTighteningClosureSeriesReview

namespace MGAP4D

structure PostR1R7ProofObligationTighteningClosure where
  r1r7ClosureSeriesReviewGreen : Prop
  proofObligationTighteningStageClosedAtReviewSurface : Prop
  r1r7TheoremRoutesStillOpen : Prop
  theoremCompletionsNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  publicBoundaryHeld : Prop

def PostR1R7ProofObligationTighteningClosure.ready
    (C : PostR1R7ProofObligationTighteningClosure) : Prop :=
  C.r1r7ClosureSeriesReviewGreen ∧
  C.proofObligationTighteningStageClosedAtReviewSurface ∧
  C.r1r7TheoremRoutesStillOpen ∧ C.theoremCompletionsNotClaimed ∧
  C.finalGapReleaseNotUnlocked ∧ C.mainPreMathlib ∧
  C.mathlibMainAdoptionHeld ∧ C.publicBoundaryHeld

theorem post_r1_r7_proof_obligation_tightening_closure_pack
    (C : PostR1R7ProofObligationTighteningClosure) :
    C.ready ↔ C.r1r7ClosureSeriesReviewGreen ∧
      C.proofObligationTighteningStageClosedAtReviewSurface ∧
      C.r1r7TheoremRoutesStillOpen ∧ C.theoremCompletionsNotClaimed ∧
      C.finalGapReleaseNotUnlocked ∧ C.mainPreMathlib ∧
      C.mathlibMainAdoptionHeld ∧ C.publicBoundaryHeld := by
  rfl

end MGAP4D
