namespace MGAP4D

structure R1R2ProofObligationTighteningBridge where
  r1TheoremCandidateSurfaceExists : Prop
  r2TheoremCandidateSurfaceExists : Prop
  r1MathlibDryRunCovered : Prop
  r2MathlibDryRunCovered : Prop
  r1NotIncludedInR3R7TighteningClosure : Prop
  r2NotIncludedInR3R7TighteningClosure : Prop
  r1TighteningReviewRequired : Prop
  r2TighteningReviewRequired : Prop
  r1r2BridgeReviewRequiredBeforeReleaseGateOpening : Prop
  r1r7ClosureSeriesReviewRequiredBeforeReleaseTag : Prop
  r1TheoremCompletionNotClaimed : Prop
  r2TheoremCompletionNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  publicBoundaryHeld : Prop

def R1R2ProofObligationTighteningBridge.ready
    (B : R1R2ProofObligationTighteningBridge) : Prop :=
  B.r1TheoremCandidateSurfaceExists ∧ B.r2TheoremCandidateSurfaceExists ∧
  B.r1MathlibDryRunCovered ∧ B.r2MathlibDryRunCovered ∧
  B.r1NotIncludedInR3R7TighteningClosure ∧ B.r2NotIncludedInR3R7TighteningClosure ∧
  B.r1TighteningReviewRequired ∧ B.r2TighteningReviewRequired ∧
  B.r1r2BridgeReviewRequiredBeforeReleaseGateOpening ∧
  B.r1r7ClosureSeriesReviewRequiredBeforeReleaseTag ∧
  B.r1TheoremCompletionNotClaimed ∧ B.r2TheoremCompletionNotClaimed ∧
  B.finalGapReleaseNotUnlocked ∧ B.mainPreMathlib ∧ B.mathlibMainAdoptionHeld ∧
  B.publicBoundaryHeld

theorem r1_r2_proof_obligation_tightening_bridge_pack
    (B : R1R2ProofObligationTighteningBridge) :
    B.ready ↔ B.r1TheoremCandidateSurfaceExists ∧ B.r2TheoremCandidateSurfaceExists ∧
      B.r1MathlibDryRunCovered ∧ B.r2MathlibDryRunCovered ∧
      B.r1NotIncludedInR3R7TighteningClosure ∧ B.r2NotIncludedInR3R7TighteningClosure ∧
      B.r1TighteningReviewRequired ∧ B.r2TighteningReviewRequired ∧
      B.r1r2BridgeReviewRequiredBeforeReleaseGateOpening ∧
      B.r1r7ClosureSeriesReviewRequiredBeforeReleaseTag ∧
      B.r1TheoremCompletionNotClaimed ∧ B.r2TheoremCompletionNotClaimed ∧
      B.finalGapReleaseNotUnlocked ∧ B.mainPreMathlib ∧ B.mathlibMainAdoptionHeld ∧
      B.publicBoundaryHeld := by
  rfl

end MGAP4D
