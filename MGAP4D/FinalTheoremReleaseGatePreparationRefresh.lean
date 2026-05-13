import MGAP4D.PostR1R7ProofObligationTighteningClosure

namespace MGAP4D

structure FinalTheoremReleaseGatePreparationRefresh where
  postR1R7ProofObligationTighteningClosureGreen : Prop
  r1r7ClosureSeriesReviewGreen : Prop
  independentReplayRequired : Prop
  externalAuditRequired : Prop
  r1r7TheoremRouteCompletionReviewRequired : Prop
  finalAssemblyReviewRequired : Prop
  publicTheoremBoundaryReviewRequired : Prop
  mathlibMainAdoptionProposalSeparate : Prop
  releaseTagProposalSeparate : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  theoremCompletionsNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def FinalTheoremReleaseGatePreparationRefresh.ready
    (G : FinalTheoremReleaseGatePreparationRefresh) : Prop :=
  G.postR1R7ProofObligationTighteningClosureGreen ∧
  G.r1r7ClosureSeriesReviewGreen ∧ G.independentReplayRequired ∧
  G.externalAuditRequired ∧ G.r1r7TheoremRouteCompletionReviewRequired ∧
  G.finalAssemblyReviewRequired ∧ G.publicTheoremBoundaryReviewRequired ∧
  G.mathlibMainAdoptionProposalSeparate ∧ G.releaseTagProposalSeparate ∧
  G.mainPreMathlib ∧ G.mathlibMainAdoptionHeld ∧
  G.theoremCompletionsNotClaimed ∧ G.finalGapReleaseNotUnlocked ∧ G.publicBoundaryHeld

theorem final_theorem_release_gate_preparation_refresh_pack
    (G : FinalTheoremReleaseGatePreparationRefresh) :
    G.ready ↔ G.postR1R7ProofObligationTighteningClosureGreen ∧
      G.r1r7ClosureSeriesReviewGreen ∧ G.independentReplayRequired ∧
      G.externalAuditRequired ∧ G.r1r7TheoremRouteCompletionReviewRequired ∧
      G.finalAssemblyReviewRequired ∧ G.publicTheoremBoundaryReviewRequired ∧
      G.mathlibMainAdoptionProposalSeparate ∧ G.releaseTagProposalSeparate ∧
      G.mainPreMathlib ∧ G.mathlibMainAdoptionHeld ∧
      G.theoremCompletionsNotClaimed ∧ G.finalGapReleaseNotUnlocked ∧ G.publicBoundaryHeld := by
  rfl

end MGAP4D
