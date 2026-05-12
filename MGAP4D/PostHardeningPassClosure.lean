import MGAP4D.R3R7HardeningPassSeriesReview

namespace MGAP4D

structure PostHardeningPassClosure where
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  hardeningPassSeriesGreen : Prop
  passLevelSegmentClosed : Prop
  theoremRoutesStillOpen : Prop
  theoremCompletionNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def PostHardeningPassClosure.ready (C : PostHardeningPassClosure) : Prop :=
  C.mainPreMathlib ∧ C.mathlibMainAdoptionHeld ∧
  C.hardeningPassSeriesGreen ∧ C.passLevelSegmentClosed ∧
  C.theoremRoutesStillOpen ∧ C.theoremCompletionNotClaimed ∧
  C.finalGapReleaseNotUnlocked ∧ C.publicBoundaryHeld

theorem post_hardening_pass_closure_pack (C : PostHardeningPassClosure) :
    C.ready ↔ C.mainPreMathlib ∧ C.mathlibMainAdoptionHeld ∧
      C.hardeningPassSeriesGreen ∧ C.passLevelSegmentClosed ∧
      C.theoremRoutesStillOpen ∧ C.theoremCompletionNotClaimed ∧
      C.finalGapReleaseNotUnlocked ∧ C.publicBoundaryHeld := by
  rfl

end MGAP4D
