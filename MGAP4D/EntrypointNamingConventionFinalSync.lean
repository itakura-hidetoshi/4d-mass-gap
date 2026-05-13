import MGAP4D.EntrypointNamingConvention

namespace MGAP4D

structure EntrypointNamingConventionFinalSync where
  namingConventionVisible : Prop
  globalTopLevelLeanRootIsMGAP4DLean : Prop
  globalPhase3GateRootIsPhase3ReleaseGate : Prop
  r2RestrictionRouteEntrypointIsR2TheoremLean : Prop
  r2EntrypointIsRouteLocal : Prop
  r2EntrypointNotGlobalRoot : Prop
  ambiguousR2TheoremRootAvoidedInGlobalContext : Prop
  globalGatesCarriedByPhase3ReleaseGate : Prop
  fullProjectImportRootIsMGAP4DLean : Prop
  theoremCompletionsNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  mainPreMathlib : Prop

def EntrypointNamingConventionFinalSync.ready
    (N : EntrypointNamingConventionFinalSync) : Prop :=
  N.namingConventionVisible ∧ N.globalTopLevelLeanRootIsMGAP4DLean ∧
  N.globalPhase3GateRootIsPhase3ReleaseGate ∧
  N.r2RestrictionRouteEntrypointIsR2TheoremLean ∧ N.r2EntrypointIsRouteLocal ∧
  N.r2EntrypointNotGlobalRoot ∧ N.ambiguousR2TheoremRootAvoidedInGlobalContext ∧
  N.globalGatesCarriedByPhase3ReleaseGate ∧ N.fullProjectImportRootIsMGAP4DLean ∧
  N.theoremCompletionsNotClaimed ∧ N.finalGapReleaseNotUnlocked ∧ N.mainPreMathlib

theorem entrypoint_naming_convention_final_sync_pack
    (N : EntrypointNamingConventionFinalSync) :
    N.ready ↔ N.namingConventionVisible ∧ N.globalTopLevelLeanRootIsMGAP4DLean ∧
      N.globalPhase3GateRootIsPhase3ReleaseGate ∧
      N.r2RestrictionRouteEntrypointIsR2TheoremLean ∧ N.r2EntrypointIsRouteLocal ∧
      N.r2EntrypointNotGlobalRoot ∧ N.ambiguousR2TheoremRootAvoidedInGlobalContext ∧
      N.globalGatesCarriedByPhase3ReleaseGate ∧ N.fullProjectImportRootIsMGAP4DLean ∧
      N.theoremCompletionsNotClaimed ∧ N.finalGapReleaseNotUnlocked ∧ N.mainPreMathlib := by
  rfl

end MGAP4D
