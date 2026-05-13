import MGAP4D.IndependentReplayGatePreparation

namespace MGAP4D

structure IndependentReplayProtocol where
  independentReplayGatePreparationGreen : Prop
  cleanCheckoutStepFixed : Prop
  leanToolchainPinStepFixed : Prop
  manifestAuditStepFixed : Prop
  forbiddenTokenAuditStepFixed : Prop
  replaySummaryStepFixed : Prop
  lakeUpdateStepFixed : Prop
  lakeBuildStepFixed : Prop
  ciLogPinStepFixed : Prop
  commitHashPinStepFixed : Prop
  replayResultNotUpgradedToTheoremCompletion : Prop
  externalAuditStillRequired : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  theoremCompletionsNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def IndependentReplayProtocol.ready
    (P : IndependentReplayProtocol) : Prop :=
  P.independentReplayGatePreparationGreen ∧
  P.cleanCheckoutStepFixed ∧ P.leanToolchainPinStepFixed ∧
  P.manifestAuditStepFixed ∧ P.forbiddenTokenAuditStepFixed ∧
  P.replaySummaryStepFixed ∧ P.lakeUpdateStepFixed ∧ P.lakeBuildStepFixed ∧
  P.ciLogPinStepFixed ∧ P.commitHashPinStepFixed ∧
  P.replayResultNotUpgradedToTheoremCompletion ∧ P.externalAuditStillRequired ∧
  P.mainPreMathlib ∧ P.mathlibMainAdoptionHeld ∧ P.theoremCompletionsNotClaimed ∧
  P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld

theorem independent_replay_protocol_pack
    (P : IndependentReplayProtocol) :
    P.ready ↔ P.independentReplayGatePreparationGreen ∧
      P.cleanCheckoutStepFixed ∧ P.leanToolchainPinStepFixed ∧
      P.manifestAuditStepFixed ∧ P.forbiddenTokenAuditStepFixed ∧
      P.replaySummaryStepFixed ∧ P.lakeUpdateStepFixed ∧ P.lakeBuildStepFixed ∧
      P.ciLogPinStepFixed ∧ P.commitHashPinStepFixed ∧
      P.replayResultNotUpgradedToTheoremCompletion ∧ P.externalAuditStillRequired ∧
      P.mainPreMathlib ∧ P.mathlibMainAdoptionHeld ∧ P.theoremCompletionsNotClaimed ∧
      P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld := by
  rfl

end MGAP4D
