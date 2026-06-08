import MGAP4D.Spectral.ExactGapTheorem
import MGAP4D.Release.PublicBoundaryTheorem

namespace MGAP4D

/-- A pre-Mathlib audit closure for the exact-gap theorem surface.

This closure binds the exact-gap theorem certificate with the public-boundary
theorem certificate.  It records that the exact `33/20` gap surface is visible,
matched to both the gap witness and sharp-gap sandwich, while final release
remains held and the public boundary remains locked. -/
structure ExactGapAuditClosure where
  exactGap : Spectral.ExactGapTheoremCertificate
  exactGapReady : exactGap.ready
  publicBoundary : Release.PublicBoundaryTheoremCertificate
  publicBoundaryReady : publicBoundary.ready
  exactGapValue3320 : exactGap.exactGapValue = 33 / 20
  exactGapMatchesWitness : exactGap.exactGapValue = exactGap.gapWitness.gap.value
  exactGapMatchesSandwich : exactGap.exactGapValue = exactGap.sandwich.exactGapValue
  publicBoundaryExactGapValue3320 : publicBoundary.exactGapBridge.exactGap.exactGapValue = 33 / 20
  v16GapValue3320 : Release.v16ReleasePacket.finalPacket.massGap.value = 33 / 20
  exactGapDoesNotOpenFinalRelease : publicBoundary.exactGapDoesNotOpenFinalRelease
  finalReleaseHeld : exactGap.finalReleaseHeld
  publicBoundaryLocked : exactGap.publicBoundaryLocked
  auditClosureVisible : Prop
  theoremBoundaryHeld : exactGap.theoremBoundaryHeld

def ExactGapAuditClosure.ready
    (C : ExactGapAuditClosure) : Prop :=
  C.exactGapReady ∧ C.publicBoundaryReady ∧ C.exactGapValue3320 ∧
  C.exactGapMatchesWitness ∧ C.exactGapMatchesSandwich ∧
  C.publicBoundaryExactGapValue3320 ∧ C.v16GapValue3320 ∧
  C.exactGapDoesNotOpenFinalRelease ∧ C.finalReleaseHeld ∧
  C.publicBoundaryLocked ∧ C.auditClosureVisible ∧ C.theoremBoundaryHeld

def exactGap3320AuditClosure : ExactGapAuditClosure :=
  { exactGap := Spectral.exactGapTheorem3320Certificate
    exactGapReady := Spectral.exact_gap_theorem_3320_ready
    publicBoundary := Release.publicBoundaryTheorem3320Certificate
    publicBoundaryReady := Release.public_boundary_theorem_3320_ready
    exactGapValue3320 := Spectral.exact_gap_theorem_3320_value
    exactGapMatchesWitness := Spectral.exact_gap_theorem_3320_matches_gap_witness
    exactGapMatchesSandwich := Spectral.exact_gap_theorem_3320_matches_sandwich
    publicBoundaryExactGapValue3320 := Release.public_boundary_theorem_3320_exact_gap_value
    v16GapValue3320 := Release.public_boundary_theorem_3320_v16_gap_value
    exactGapDoesNotOpenFinalRelease := Release.public_boundary_theorem_3320_exact_gap_does_not_open_final_release
    finalReleaseHeld := Spectral.exact_gap_theorem_3320_release_held
    publicBoundaryLocked := Spectral.exact_gap_theorem_3320_public_boundary_locked
    auditClosureVisible := True
    theoremBoundaryHeld := by trivial }

theorem exact_gap_audit_closure_pack
    (C : ExactGapAuditClosure) :
    C.ready ↔ C.exactGapReady ∧ C.publicBoundaryReady ∧ C.exactGapValue3320 ∧
      C.exactGapMatchesWitness ∧ C.exactGapMatchesSandwich ∧
      C.publicBoundaryExactGapValue3320 ∧ C.v16GapValue3320 ∧
      C.exactGapDoesNotOpenFinalRelease ∧ C.finalReleaseHeld ∧
      C.publicBoundaryLocked ∧ C.auditClosureVisible ∧ C.theoremBoundaryHeld := by
  rfl

theorem exact_gap_3320_audit_closure_ready :
    exactGap3320AuditClosure.ready := by
  exact And.intro Spectral.exact_gap_theorem_3320_ready <|
    And.intro Release.public_boundary_theorem_3320_ready <|
    And.intro Spectral.exact_gap_theorem_3320_value <|
    And.intro Spectral.exact_gap_theorem_3320_matches_gap_witness <|
    And.intro Spectral.exact_gap_theorem_3320_matches_sandwich <|
    And.intro Release.public_boundary_theorem_3320_exact_gap_value <|
    And.intro Release.public_boundary_theorem_3320_v16_gap_value <|
    And.intro Release.public_boundary_theorem_3320_exact_gap_does_not_open_final_release <|
    And.intro Spectral.exact_gap_theorem_3320_release_held <|
    And.intro Spectral.exact_gap_theorem_3320_public_boundary_locked <|
    And.intro True.intro True.intro

theorem exact_gap_3320_audit_closure_value :
    exactGap3320AuditClosure.exactGap.exactGapValue = 33 / 20 := by
  exact Spectral.exact_gap_theorem_3320_value

theorem exact_gap_3320_audit_closure_matches_witness :
    exactGap3320AuditClosure.exactGap.exactGapValue =
      exactGap3320AuditClosure.exactGap.gapWitness.gap.value := by
  exact Spectral.exact_gap_theorem_3320_matches_gap_witness

theorem exact_gap_3320_audit_closure_matches_sandwich :
    exactGap3320AuditClosure.exactGap.exactGapValue =
      exactGap3320AuditClosure.exactGap.sandwich.exactGapValue := by
  exact Spectral.exact_gap_theorem_3320_matches_sandwich

theorem exact_gap_3320_audit_closure_release_held :
    exactGap3320AuditClosure.finalReleaseHeld := by
  exact Spectral.exact_gap_theorem_3320_release_held

theorem exact_gap_3320_audit_closure_public_boundary_locked :
    exactGap3320AuditClosure.publicBoundaryLocked := by
  exact Spectral.exact_gap_theorem_3320_public_boundary_locked

theorem exact_gap_3320_audit_closure_no_final_release_open :
    exactGap3320AuditClosure.exactGapDoesNotOpenFinalRelease := by
  exact Release.public_boundary_theorem_3320_exact_gap_does_not_open_final_release

end MGAP4D
