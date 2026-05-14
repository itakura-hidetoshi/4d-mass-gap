import MGAP4D.SpectralFinalReleaseHold

namespace MGAP4D

/-- A pre-Mathlib public-boundary lock for the spectral chain.

This lock records that the spectral chain remains review-gated even after the
release-readiness and hold layers are visible. -/
structure SpectralPublicBoundaryLock where
  hold : SpectralFinalReleaseHold
  holdReady : hold.ready
  publicBoundaryLocked : Prop
  reviewGateStillRequired : Prop
  replayStillRequired : Prop
  sourceTreeReviewStillRequired : Prop
  externalAuditStillRequired : Prop
  theoremCompletionsNotClaimed : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop

def SpectralPublicBoundaryLock.ready
    (L : SpectralPublicBoundaryLock) : Prop :=
  L.holdReady ∧ L.publicBoundaryLocked ∧ L.reviewGateStillRequired ∧
  L.replayStillRequired ∧ L.sourceTreeReviewStillRequired ∧
  L.externalAuditStillRequired ∧ L.theoremCompletionsNotClaimed ∧
  L.mainPreMathlib ∧ L.mathlibMainAdoptionHeld

def spectral3320PublicBoundaryLock : SpectralPublicBoundaryLock :=
  { hold := spectral3320FinalReleaseHold
    holdReady := spectral3320_final_release_hold_ready
    publicBoundaryLocked := True
    reviewGateStillRequired := True
    replayStillRequired := True
    sourceTreeReviewStillRequired := True
    externalAuditStillRequired := True
    theoremCompletionsNotClaimed := True
    mainPreMathlib := True
    mathlibMainAdoptionHeld := True }

theorem spectral_public_boundary_lock_pack
    (L : SpectralPublicBoundaryLock) :
    L.ready ↔ L.holdReady ∧ L.publicBoundaryLocked ∧ L.reviewGateStillRequired ∧
      L.replayStillRequired ∧ L.sourceTreeReviewStillRequired ∧
      L.externalAuditStillRequired ∧ L.theoremCompletionsNotClaimed ∧
      L.mainPreMathlib ∧ L.mathlibMainAdoptionHeld := by
  rfl

theorem spectral3320_public_boundary_lock_ready :
    spectral3320PublicBoundaryLock.ready := by
  exact And.intro spectral3320_final_release_hold_ready <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem spectral3320_public_boundary_lock_value :
    spectral3320PublicBoundaryLock.hold.closure.readiness.spine.bridge.coreCertificate.formalization.normalizedGapValue.value = 33 / 20 := by
  rfl

theorem spectral3320_public_boundary_lock_positive_numerator :
    spectral3320PublicBoundaryLock.hold.closure.readiness.spine.bridge.coreCertificate.lowerBound.positiveGap.witness.gap.value.num > 0 := by
  exact Spectral.gap3320Witness.positiveNumerator

theorem spectral3320_public_boundary_is_locked :
    spectral3320PublicBoundaryLock.publicBoundaryLocked := by
  trivial

end MGAP4D
