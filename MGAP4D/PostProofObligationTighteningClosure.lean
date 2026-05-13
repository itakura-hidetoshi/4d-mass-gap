import MGAP4D.R3R7ProofObligationTighteningClosureSeriesReview

namespace MGAP4D

structure PostProofObligationTighteningClosure where
  r3r7ClosureSeriesReviewGreen : Prop
  proofObligationTighteningStageClosedAtReviewSurface : Prop
  theoremRoutesStillOpen : Prop
  theoremCompletionsNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  publicBoundaryHeld : Prop

def PostProofObligationTighteningClosure.ready
    (C : PostProofObligationTighteningClosure) : Prop :=
  C.r3r7ClosureSeriesReviewGreen ∧
  C.proofObligationTighteningStageClosedAtReviewSurface ∧
  C.theoremRoutesStillOpen ∧ C.theoremCompletionsNotClaimed ∧
  C.finalGapReleaseNotUnlocked ∧ C.mainPreMathlib ∧
  C.mathlibMainAdoptionHeld ∧ C.publicBoundaryHeld

theorem post_proof_obligation_tightening_closure_pack
    (C : PostProofObligationTighteningClosure) :
    C.ready ↔ C.r3r7ClosureSeriesReviewGreen ∧
      C.proofObligationTighteningStageClosedAtReviewSurface ∧
      C.theoremRoutesStillOpen ∧ C.theoremCompletionsNotClaimed ∧
      C.finalGapReleaseNotUnlocked ∧ C.mainPreMathlib ∧
      C.mathlibMainAdoptionHeld ∧ C.publicBoundaryHeld := by
  rfl

end MGAP4D
