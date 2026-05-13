import MGAP4D.R1R7ProofObligationTighteningClosureSeriesReview
import MGAP4D.PostR1R7ProofObligationTighteningClosure
import MGAP4D.FinalTheoremReleaseGatePreparationRefresh
import MGAP4D.IndependentReplayGatePreparation
import MGAP4D.IndependentReplayProtocol
import MGAP4D.SourceTreeReviewGate
import MGAP4D.SourceTreeReviewGateFinalSync

namespace MGAP4D

structure Phase3ReleaseGateRoot where
  r1r7ClosureSeriesReviewVisible : Prop
  postR1R7ClosureVisible : Prop
  finalReleaseGatePreparationRefreshVisible : Prop
  independentReplayGatePreparationVisible : Prop
  independentReplayProtocolVisible : Prop
  sourceTreeReviewGateVisible : Prop
  sourceTreeReviewGateFinalSyncVisible : Prop
  globalGateRootNotR2Local : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  theoremCompletionsNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def Phase3ReleaseGateRoot.ready
    (G : Phase3ReleaseGateRoot) : Prop :=
  G.r1r7ClosureSeriesReviewVisible ∧ G.postR1R7ClosureVisible ∧
  G.finalReleaseGatePreparationRefreshVisible ∧ G.independentReplayGatePreparationVisible ∧
  G.independentReplayProtocolVisible ∧ G.sourceTreeReviewGateVisible ∧
  G.sourceTreeReviewGateFinalSyncVisible ∧ G.globalGateRootNotR2Local ∧
  G.mainPreMathlib ∧ G.mathlibMainAdoptionHeld ∧
  G.theoremCompletionsNotClaimed ∧ G.finalGapReleaseNotUnlocked ∧ G.publicBoundaryHeld

theorem phase3_release_gate_root_pack
    (G : Phase3ReleaseGateRoot) :
    G.ready ↔ G.r1r7ClosureSeriesReviewVisible ∧ G.postR1R7ClosureVisible ∧
      G.finalReleaseGatePreparationRefreshVisible ∧ G.independentReplayGatePreparationVisible ∧
      G.independentReplayProtocolVisible ∧ G.sourceTreeReviewGateVisible ∧
      G.sourceTreeReviewGateFinalSyncVisible ∧ G.globalGateRootNotR2Local ∧
      G.mainPreMathlib ∧ G.mathlibMainAdoptionHeld ∧
      G.theoremCompletionsNotClaimed ∧ G.finalGapReleaseNotUnlocked ∧ G.publicBoundaryHeld := by
  rfl

end MGAP4D
