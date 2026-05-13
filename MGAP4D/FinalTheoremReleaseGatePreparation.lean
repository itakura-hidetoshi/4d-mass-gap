import MGAP4D.PostProofObligationTighteningClosure

namespace MGAP4D

structure FinalTheoremReleaseGatePreparation where
  postProofObligationTighteningClosureGreen : Prop
  independentReplayRequired : Prop
  externalAuditRequired : Prop
  r3r7TheoremRouteCompletionReviewRequired : Prop
  finalAssemblyReviewRequired : Prop
  publicTheoremBoundaryReviewRequired : Prop
  mathlibMainAdoptionProposalSeparate : Prop
  releaseTagProposalSeparate : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  theoremCompletionsNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def FinalTheoremReleaseGatePreparation.ready
    (G : FinalTheoremReleaseGatePreparation) : Prop :=
  G.postProofObligationTighteningClosureGreen ∧
  G.independentReplayRequired ∧ G.externalAuditRequired ∧
  G.r3r7TheoremRouteCompletionReviewRequired ∧ G.finalAssemblyReviewRequired ∧
  G.publicTheoremBoundaryReviewRequired ∧ G.mathlibMainAdoptionProposalSeparate ∧
  G.releaseTagProposalSeparate ∧ G.mainPreMathlib ∧ G.mathlibMainAdoptionHeld ∧
  G.theoremCompletionsNotClaimed ∧ G.finalGapReleaseNotUnlocked ∧ G.publicBoundaryHeld

theorem final_theorem_release_gate_preparation_pack
    (G : FinalTheoremReleaseGatePreparation) :
    G.ready ↔ G.postProofObligationTighteningClosureGreen ∧
      G.independentReplayRequired ∧ G.externalAuditRequired ∧
      G.r3r7TheoremRouteCompletionReviewRequired ∧ G.finalAssemblyReviewRequired ∧
      G.publicTheoremBoundaryReviewRequired ∧ G.mathlibMainAdoptionProposalSeparate ∧
      G.releaseTagProposalSeparate ∧ G.mainPreMathlib ∧ G.mathlibMainAdoptionHeld ∧
      G.theoremCompletionsNotClaimed ∧ G.finalGapReleaseNotUnlocked ∧ G.publicBoundaryHeld := by
  rfl

end MGAP4D
