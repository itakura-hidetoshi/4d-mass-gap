namespace MGAP4D

structure EntrypointNamingConvention where
  globalTopLevelLeanRootIsMGAP4DLean : Prop
  globalPhase3GateRootIsPhase3ReleaseGate : Prop
  r2RestrictionRouteEntrypointIsR2TheoremLean : Prop
  r2EntrypointIsRouteLocal : Prop
  r2EntrypointNotGlobalRoot : Prop
  avoidAmbiguousR2TheoremRootInGlobalContext : Prop
  useR2EntrypointForR2TheoremLean : Prop
  useGlobalTopLevelRootForMGAP4DLean : Prop
  useGlobalPhase3GateRootForPhase3ReleaseGate : Prop
  globalGatesCarriedByPhase3ReleaseGate : Prop
  theoremCompletionsNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  mainPreMathlib : Prop

def EntrypointNamingConvention.ready
    (N : EntrypointNamingConvention) : Prop :=
  N.globalTopLevelLeanRootIsMGAP4DLean ∧
  N.globalPhase3GateRootIsPhase3ReleaseGate ∧
  N.r2RestrictionRouteEntrypointIsR2TheoremLean ∧
  N.r2EntrypointIsRouteLocal ∧ N.r2EntrypointNotGlobalRoot ∧
  N.avoidAmbiguousR2TheoremRootInGlobalContext ∧
  N.useR2EntrypointForR2TheoremLean ∧
  N.useGlobalTopLevelRootForMGAP4DLean ∧
  N.useGlobalPhase3GateRootForPhase3ReleaseGate ∧
  N.globalGatesCarriedByPhase3ReleaseGate ∧
  N.theoremCompletionsNotClaimed ∧ N.finalGapReleaseNotUnlocked ∧ N.mainPreMathlib

theorem entrypoint_naming_convention_pack
    (N : EntrypointNamingConvention) :
    N.ready ↔ N.globalTopLevelLeanRootIsMGAP4DLean ∧
      N.globalPhase3GateRootIsPhase3ReleaseGate ∧
      N.r2RestrictionRouteEntrypointIsR2TheoremLean ∧
      N.r2EntrypointIsRouteLocal ∧ N.r2EntrypointNotGlobalRoot ∧
      N.avoidAmbiguousR2TheoremRootInGlobalContext ∧
      N.useR2EntrypointForR2TheoremLean ∧
      N.useGlobalTopLevelRootForMGAP4DLean ∧
      N.useGlobalPhase3GateRootForPhase3ReleaseGate ∧
      N.globalGatesCarriedByPhase3ReleaseGate ∧
      N.theoremCompletionsNotClaimed ∧ N.finalGapReleaseNotUnlocked ∧ N.mainPreMathlib := by
  rfl

end MGAP4D
