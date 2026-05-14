import MGAP4D.ExactGapAuditClosure

namespace MGAP4D

/-- A pre-Mathlib release-readiness layer for the exact-gap theorem surface.

This layer records that the exact-gap audit closure is ready for external
review/replay while the public final theorem release remains held.  It separates
"audit/review readiness" from "public final release". -/
structure ExactGapReleaseReadiness where
  auditClosure : ExactGapAuditClosure
  auditClosureReady : auditClosure.ready
  exactGapSurfaceReady : auditClosure.exactGapReady
  publicBoundarySurfaceReady : auditClosure.publicBoundaryReady
  exactGapValue3320 : auditClosure.exactGap.exactGapValue = 33 / 20
  exactGapMatchesWitness : auditClosure.exactGap.exactGapValue = auditClosure.exactGap.gapWitness.gap.value
  exactGapMatchesSandwich : auditClosure.exactGap.exactGapValue = auditClosure.exactGap.sandwich.exactGapValue
  externalAuditReadinessVisible : Prop
  reviewReplayReady : Prop
  finalReleaseHeld : auditClosure.finalReleaseHeld
  publicBoundaryLocked : auditClosure.publicBoundaryLocked
  exactGapDoesNotOpenFinalRelease : auditClosure.exactGapDoesNotOpenFinalRelease
  theoremBoundaryHeld : auditClosure.theoremBoundaryHeld

def ExactGapReleaseReadiness.ready
    (R : ExactGapReleaseReadiness) : Prop :=
  R.auditClosureReady ∧ R.exactGapSurfaceReady ∧ R.publicBoundarySurfaceReady ∧
  R.exactGapValue3320 ∧ R.exactGapMatchesWitness ∧ R.exactGapMatchesSandwich ∧
  R.externalAuditReadinessVisible ∧ R.reviewReplayReady ∧ R.finalReleaseHeld ∧
  R.publicBoundaryLocked ∧ R.exactGapDoesNotOpenFinalRelease ∧ R.theoremBoundaryHeld

def exactGap3320ReleaseReadiness : ExactGapReleaseReadiness :=
  { auditClosure := exactGap3320AuditClosure
    auditClosureReady := exact_gap_3320_audit_closure_ready
    exactGapSurfaceReady := Spectral.exact_gap_theorem_3320_ready
    publicBoundarySurfaceReady := Release.public_boundary_theorem_3320_ready
    exactGapValue3320 := exact_gap_3320_audit_closure_value
    exactGapMatchesWitness := exact_gap_3320_audit_closure_matches_witness
    exactGapMatchesSandwich := exact_gap_3320_audit_closure_matches_sandwich
    externalAuditReadinessVisible := True
    reviewReplayReady := True
    finalReleaseHeld := exact_gap_3320_audit_closure_release_held
    publicBoundaryLocked := exact_gap_3320_audit_closure_public_boundary_locked
    exactGapDoesNotOpenFinalRelease := exact_gap_3320_audit_closure_no_final_release_open
    theoremBoundaryHeld := by trivial }

theorem exact_gap_release_readiness_pack
    (R : ExactGapReleaseReadiness) :
    R.ready ↔ R.auditClosureReady ∧ R.exactGapSurfaceReady ∧
      R.publicBoundarySurfaceReady ∧ R.exactGapValue3320 ∧ R.exactGapMatchesWitness ∧
      R.exactGapMatchesSandwich ∧ R.externalAuditReadinessVisible ∧ R.reviewReplayReady ∧
      R.finalReleaseHeld ∧ R.publicBoundaryLocked ∧ R.exactGapDoesNotOpenFinalRelease ∧
      R.theoremBoundaryHeld := by
  rfl

theorem exact_gap_3320_release_readiness_ready :
    exactGap3320ReleaseReadiness.ready := by
  exact And.intro exact_gap_3320_audit_closure_ready <|
    And.intro Spectral.exact_gap_theorem_3320_ready <|
    And.intro Release.public_boundary_theorem_3320_ready <|
    And.intro exact_gap_3320_audit_closure_value <|
    And.intro exact_gap_3320_audit_closure_matches_witness <|
    And.intro exact_gap_3320_audit_closure_matches_sandwich <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro exact_gap_3320_audit_closure_release_held <|
    And.intro exact_gap_3320_audit_closure_public_boundary_locked <|
    And.intro exact_gap_3320_audit_closure_no_final_release_open True.intro

theorem exact_gap_3320_release_readiness_value :
    exactGap3320ReleaseReadiness.auditClosure.exactGap.exactGapValue = 33 / 20 := by
  exact exact_gap_3320_audit_closure_value

theorem exact_gap_3320_release_readiness_matches_witness :
    exactGap3320ReleaseReadiness.auditClosure.exactGap.exactGapValue =
      exactGap3320ReleaseReadiness.auditClosure.exactGap.gapWitness.gap.value := by
  exact exact_gap_3320_audit_closure_matches_witness

theorem exact_gap_3320_release_readiness_matches_sandwich :
    exactGap3320ReleaseReadiness.auditClosure.exactGap.exactGapValue =
      exactGap3320ReleaseReadiness.auditClosure.exactGap.sandwich.exactGapValue := by
  exact exact_gap_3320_audit_closure_matches_sandwich

theorem exact_gap_3320_release_readiness_release_held :
    exactGap3320ReleaseReadiness.finalReleaseHeld := by
  exact exact_gap_3320_audit_closure_release_held

theorem exact_gap_3320_release_readiness_public_boundary_locked :
    exactGap3320ReleaseReadiness.publicBoundaryLocked := by
  exact exact_gap_3320_audit_closure_public_boundary_locked

theorem exact_gap_3320_release_readiness_no_auto_release :
    exactGap3320ReleaseReadiness.exactGapDoesNotOpenFinalRelease := by
  exact exact_gap_3320_audit_closure_no_final_release_open

end MGAP4D
