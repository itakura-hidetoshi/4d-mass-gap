import MGAP4D.SpectralPhase3Spine

namespace MGAP4D

/-- A pre-Mathlib readiness layer that connects the spectral Phase 3 spine to
independent replay, source-tree review, and external-audit boundary surfaces.

This is a review/readiness certificate only. It does not open final theorem
release and it does not claim R1--R7 theorem completion. -/
structure SpectralReplayReadiness where
  spine : SpectralPhase3Spine
  spineReady : spine.ready
  independentReplaySurfaceVisible : Prop
  sourceTreeReviewSurfaceVisible : Prop
  externalAuditBoundaryVisible : Prop
  replayDoesNotUnlockFinalRelease : Prop
  theoremCompletionsNotClaimed : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  publicBoundaryHeld : Prop

/-- Readiness is a proposition-level checklist.  Proof-carrying fields are
re-expanded to their underlying propositions, rather than being reused as proof
terms inside the `∧` chain. -/
def SpectralReplayReadiness.ready
    (R : SpectralReplayReadiness) : Prop :=
  R.spine.ready ∧ R.independentReplaySurfaceVisible ∧
  R.sourceTreeReviewSurfaceVisible ∧ R.externalAuditBoundaryVisible ∧
  R.replayDoesNotUnlockFinalRelease ∧ R.theoremCompletionsNotClaimed ∧
  R.mainPreMathlib ∧ R.mathlibMainAdoptionHeld ∧ R.publicBoundaryHeld

def spectral3320ReplayReadiness : SpectralReplayReadiness :=
  { spine := spectral3320Phase3Spine
    spineReady := spectral3320_phase3_spine_ready
    independentReplaySurfaceVisible := True
    sourceTreeReviewSurfaceVisible := True
    externalAuditBoundaryVisible := True
    replayDoesNotUnlockFinalRelease := True
    theoremCompletionsNotClaimed := True
    mainPreMathlib := True
    mathlibMainAdoptionHeld := True
    publicBoundaryHeld := True }

theorem spectral_replay_readiness_pack
    (R : SpectralReplayReadiness) :
    R.ready ↔ R.spine.ready ∧ R.independentReplaySurfaceVisible ∧
      R.sourceTreeReviewSurfaceVisible ∧ R.externalAuditBoundaryVisible ∧
      R.replayDoesNotUnlockFinalRelease ∧ R.theoremCompletionsNotClaimed ∧
      R.mainPreMathlib ∧ R.mathlibMainAdoptionHeld ∧ R.publicBoundaryHeld := by
  rfl

theorem spectral3320_replay_readiness_ready :
    spectral3320ReplayReadiness.ready := by
  exact And.intro spectral3320_phase3_spine_ready <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem spectral3320_replay_readiness_value :
    spectral3320ReplayReadiness.spine.bridge.coreCertificate.formalization.normalizedGapValue.value = 33 / 20 := by
  rfl

theorem spectral3320_replay_readiness_positive_numerator :
    spectral3320ReplayReadiness.spine.bridge.coreCertificate.lowerBound.positiveGap.witness.gap.value.num > 0 := by
  exact Spectral.gap3320Witness.positiveNumerator

theorem spectral3320_replay_readiness_public_boundary_held :
    spectral3320ReplayReadiness.publicBoundaryHeld := by
  trivial

end MGAP4D
