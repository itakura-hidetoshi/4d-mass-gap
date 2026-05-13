import MGAP4D.IndependentReplayGatePreparation

namespace MGAP4D

structure IndependentReplayProtocol where
  independentReplayGatePreparationGreen : Prop
  r1ReplaySurfaceIncluded : Prop
  r2ReplaySurfaceIncluded : Prop
  r3ReplaySurfaceIncluded : Prop
  r4ReplaySurfaceIncluded : Prop
  r5ReplaySurfaceIncluded : Prop
  r6ReplaySurfaceIncluded : Prop
  r7ReplaySurfaceIncluded : Prop
  r1r7ReplaySurfaceIncluded : Prop
  protocolIsGlobalNotR2Local : Prop
  topLevelRootCarriesProtocol : Prop
  phase3ReleaseGateCarriesProtocol : Prop
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
  P.r1ReplaySurfaceIncluded ∧ P.r2ReplaySurfaceIncluded ∧
  P.r3ReplaySurfaceIncluded ∧ P.r4ReplaySurfaceIncluded ∧
  P.r5ReplaySurfaceIncluded ∧ P.r6ReplaySurfaceIncluded ∧
  P.r7ReplaySurfaceIncluded ∧ P.r1r7ReplaySurfaceIncluded ∧
  P.protocolIsGlobalNotR2Local ∧ P.topLevelRootCarriesProtocol ∧
  P.phase3ReleaseGateCarriesProtocol ∧ P.cleanCheckoutStepFixed ∧
  P.leanToolchainPinStepFixed ∧ P.manifestAuditStepFixed ∧
  P.forbiddenTokenAuditStepFixed ∧ P.replaySummaryStepFixed ∧
  P.lakeUpdateStepFixed ∧ P.lakeBuildStepFixed ∧
  P.ciLogPinStepFixed ∧ P.commitHashPinStepFixed ∧
  P.replayResultNotUpgradedToTheoremCompletion ∧ P.externalAuditStillRequired ∧
  P.mainPreMathlib ∧ P.mathlibMainAdoptionHeld ∧ P.theoremCompletionsNotClaimed ∧
  P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld

theorem independent_replay_protocol_pack
    (P : IndependentReplayProtocol) :
    P.ready ↔ P.independentReplayGatePreparationGreen ∧
      P.r1ReplaySurfaceIncluded ∧ P.r2ReplaySurfaceIncluded ∧
      P.r3ReplaySurfaceIncluded ∧ P.r4ReplaySurfaceIncluded ∧
      P.r5ReplaySurfaceIncluded ∧ P.r6ReplaySurfaceIncluded ∧
      P.r7ReplaySurfaceIncluded ∧ P.r1r7ReplaySurfaceIncluded ∧
      P.protocolIsGlobalNotR2Local ∧ P.topLevelRootCarriesProtocol ∧
      P.phase3ReleaseGateCarriesProtocol ∧ P.cleanCheckoutStepFixed ∧
      P.leanToolchainPinStepFixed ∧ P.manifestAuditStepFixed ∧
      P.forbiddenTokenAuditStepFixed ∧ P.replaySummaryStepFixed ∧
      P.lakeUpdateStepFixed ∧ P.lakeBuildStepFixed ∧
      P.ciLogPinStepFixed ∧ P.commitHashPinStepFixed ∧
      P.replayResultNotUpgradedToTheoremCompletion ∧ P.externalAuditStillRequired ∧
      P.mainPreMathlib ∧ P.mathlibMainAdoptionHeld ∧ P.theoremCompletionsNotClaimed ∧
      P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld := by
  rfl

end MGAP4D
