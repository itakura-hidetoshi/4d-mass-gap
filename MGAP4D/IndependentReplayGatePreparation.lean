import MGAP4D.FinalTheoremReleaseGatePreparationRefresh

namespace MGAP4D

structure IndependentReplayGatePreparation where
  finalTheoremReleaseGatePreparationRefreshGreen : Prop
  postR1R7ProofObligationTighteningClosureGreen : Prop
  cleanCheckoutReplayRequired : Prop
  leanToolchainPinRequired : Prop
  lakeUpdateReplayRequired : Prop
  lakeBuildReplayRequired : Prop
  auditScriptsReplayRequired : Prop
  ciLogPinRequired : Prop
  commitHashPinRequired : Prop
  sourceTreeReviewRequired : Prop
  externalAuditStillRequired : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  theoremCompletionsNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def IndependentReplayGatePreparation.ready
    (G : IndependentReplayGatePreparation) : Prop :=
  G.finalTheoremReleaseGatePreparationRefreshGreen ∧
  G.postR1R7ProofObligationTighteningClosureGreen ∧
  G.cleanCheckoutReplayRequired ∧ G.leanToolchainPinRequired ∧
  G.lakeUpdateReplayRequired ∧ G.lakeBuildReplayRequired ∧
  G.auditScriptsReplayRequired ∧ G.ciLogPinRequired ∧ G.commitHashPinRequired ∧
  G.sourceTreeReviewRequired ∧ G.externalAuditStillRequired ∧
  G.mainPreMathlib ∧ G.mathlibMainAdoptionHeld ∧ G.theoremCompletionsNotClaimed ∧
  G.finalGapReleaseNotUnlocked ∧ G.publicBoundaryHeld

theorem independent_replay_gate_preparation_pack
    (G : IndependentReplayGatePreparation) :
    G.ready ↔ G.finalTheoremReleaseGatePreparationRefreshGreen ∧
      G.postR1R7ProofObligationTighteningClosureGreen ∧
      G.cleanCheckoutReplayRequired ∧ G.leanToolchainPinRequired ∧
      G.lakeUpdateReplayRequired ∧ G.lakeBuildReplayRequired ∧
      G.auditScriptsReplayRequired ∧ G.ciLogPinRequired ∧ G.commitHashPinRequired ∧
      G.sourceTreeReviewRequired ∧ G.externalAuditStillRequired ∧
      G.mainPreMathlib ∧ G.mathlibMainAdoptionHeld ∧ G.theoremCompletionsNotClaimed ∧
      G.finalGapReleaseNotUnlocked ∧ G.publicBoundaryHeld := by
  rfl

end MGAP4D
