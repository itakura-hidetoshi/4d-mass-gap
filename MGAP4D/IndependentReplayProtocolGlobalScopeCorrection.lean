import MGAP4D.IndependentReplayProtocol

namespace MGAP4D

structure IndependentReplayProtocolGlobalScopeCorrection where
  r1ReplaySurfaceIncluded : Prop
  r2ReplaySurfaceIncluded : Prop
  r3ReplaySurfaceIncluded : Prop
  r4ReplaySurfaceIncluded : Prop
  r5ReplaySurfaceIncluded : Prop
  r6ReplaySurfaceIncluded : Prop
  r7ReplaySurfaceIncluded : Prop
  r1r7ReplaySurfaceIncluded : Prop
  protocolCarriedByPhase3ReleaseGate : Prop
  protocolCarriedByTopLevelMGAP4DRoot : Prop
  protocolNotR2Local : Prop
  r2EntrypointOnly : Prop
  globalTopLevelRootIsMGAP4DLean : Prop
  globalGateRootIsPhase3ReleaseGate : Prop
  theoremCompletionsNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  publicBoundaryHeld : Prop

def IndependentReplayProtocolGlobalScopeCorrection.ready
    (C : IndependentReplayProtocolGlobalScopeCorrection) : Prop :=
  C.r1ReplaySurfaceIncluded ∧ C.r2ReplaySurfaceIncluded ∧
  C.r3ReplaySurfaceIncluded ∧ C.r4ReplaySurfaceIncluded ∧
  C.r5ReplaySurfaceIncluded ∧ C.r6ReplaySurfaceIncluded ∧
  C.r7ReplaySurfaceIncluded ∧ C.r1r7ReplaySurfaceIncluded ∧
  C.protocolCarriedByPhase3ReleaseGate ∧ C.protocolCarriedByTopLevelMGAP4DRoot ∧
  C.protocolNotR2Local ∧ C.r2EntrypointOnly ∧
  C.globalTopLevelRootIsMGAP4DLean ∧ C.globalGateRootIsPhase3ReleaseGate ∧
  C.theoremCompletionsNotClaimed ∧ C.finalGapReleaseNotUnlocked ∧
  C.mainPreMathlib ∧ C.mathlibMainAdoptionHeld ∧ C.publicBoundaryHeld

theorem independent_replay_protocol_global_scope_correction_pack
    (C : IndependentReplayProtocolGlobalScopeCorrection) :
    C.ready ↔ C.r1ReplaySurfaceIncluded ∧ C.r2ReplaySurfaceIncluded ∧
      C.r3ReplaySurfaceIncluded ∧ C.r4ReplaySurfaceIncluded ∧
      C.r5ReplaySurfaceIncluded ∧ C.r6ReplaySurfaceIncluded ∧
      C.r7ReplaySurfaceIncluded ∧ C.r1r7ReplaySurfaceIncluded ∧
      C.protocolCarriedByPhase3ReleaseGate ∧ C.protocolCarriedByTopLevelMGAP4DRoot ∧
      C.protocolNotR2Local ∧ C.r2EntrypointOnly ∧
      C.globalTopLevelRootIsMGAP4DLean ∧ C.globalGateRootIsPhase3ReleaseGate ∧
      C.theoremCompletionsNotClaimed ∧ C.finalGapReleaseNotUnlocked ∧
      C.mainPreMathlib ∧ C.mathlibMainAdoptionHeld ∧ C.publicBoundaryHeld := by
  rfl

end MGAP4D
