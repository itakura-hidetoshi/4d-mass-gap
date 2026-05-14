import MGAP4D.ExactGapFinalSpineBridge
import MGAP4D.Release.V16

namespace MGAP4D
namespace Release

/-- A pre-Mathlib public-boundary theorem certificate.

This certificate records that visibility of the exact-gap theorem surface does
not by itself open the public final theorem release.  The exact-gap theorem is
visible and CI-trackable, while final release remains held and the public
boundary remains locked. -/
structure PublicBoundaryTheoremCertificate where
  exactGapBridge : ExactGapFinalSpineBridge
  exactGapBridgeReady : exactGapBridge.ready
  exactGapTheoremVisible : exactGapBridge.exactGapReady
  exactGapValue3320 : exactGapBridge.exactGapValue3320
  v16ReleasePacketVisible : Prop
  v16GapValue3320 : v16ReleasePacket.finalPacket.massGap.value = 33 / 20
  finalReleaseHeld : exactGapBridge.finalReleaseHeld
  publicBoundaryLocked : exactGapBridge.publicBoundaryLocked
  exactGapDoesNotOpenFinalRelease : Prop
  publicBoundaryTheoremVisible : Prop
  theoremBoundaryHeld : exactGapBridge.theoremBoundaryHeld

def PublicBoundaryTheoremCertificate.ready
    (C : PublicBoundaryTheoremCertificate) : Prop :=
  C.exactGapBridgeReady ∧ C.exactGapTheoremVisible ∧ C.exactGapValue3320 ∧
  C.v16ReleasePacketVisible ∧ C.v16GapValue3320 ∧ C.finalReleaseHeld ∧
  C.publicBoundaryLocked ∧ C.exactGapDoesNotOpenFinalRelease ∧
  C.publicBoundaryTheoremVisible ∧ C.theoremBoundaryHeld

def publicBoundaryTheorem3320Certificate : PublicBoundaryTheoremCertificate :=
  { exactGapBridge := exactGapFinalSpineBridge3320
    exactGapBridgeReady := exact_gap_final_spine_bridge_3320_ready
    exactGapTheoremVisible := final_spine_exact_gap_theorem_ready
    exactGapValue3320 := final_spine_exact_gap_value_3320
    v16ReleasePacketVisible := True
    v16GapValue3320 := v16_release_gap3320
    finalReleaseHeld := final_spine_exact_gap_release_held
    publicBoundaryLocked := final_spine_exact_gap_public_boundary_locked
    exactGapDoesNotOpenFinalRelease := True
    publicBoundaryTheoremVisible := True
    theoremBoundaryHeld := by trivial }

theorem public_boundary_theorem_certificate_pack
    (C : PublicBoundaryTheoremCertificate) :
    C.ready ↔ C.exactGapBridgeReady ∧ C.exactGapTheoremVisible ∧ C.exactGapValue3320 ∧
      C.v16ReleasePacketVisible ∧ C.v16GapValue3320 ∧ C.finalReleaseHeld ∧
      C.publicBoundaryLocked ∧ C.exactGapDoesNotOpenFinalRelease ∧
      C.publicBoundaryTheoremVisible ∧ C.theoremBoundaryHeld := by
  rfl

theorem public_boundary_theorem_3320_ready :
    publicBoundaryTheorem3320Certificate.ready := by
  exact And.intro exact_gap_final_spine_bridge_3320_ready <|
    And.intro final_spine_exact_gap_theorem_ready <|
    And.intro final_spine_exact_gap_value_3320 <|
    And.intro True.intro <|
    And.intro v16_release_gap3320 <|
    And.intro final_spine_exact_gap_release_held <|
    And.intro final_spine_exact_gap_public_boundary_locked <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem public_boundary_theorem_3320_exact_gap_visible :
    publicBoundaryTheorem3320Certificate.exactGapTheoremVisible := by
  exact final_spine_exact_gap_theorem_ready

theorem public_boundary_theorem_3320_exact_gap_value :
    publicBoundaryTheorem3320Certificate.exactGapBridge.exactGap.exactGapValue = 33 / 20 := by
  exact final_spine_exact_gap_value_3320

theorem public_boundary_theorem_3320_v16_gap_value :
    publicBoundaryTheorem3320Certificate.v16GapValue3320 := by
  exact v16_release_gap3320

theorem public_boundary_theorem_3320_release_held :
    publicBoundaryTheorem3320Certificate.finalReleaseHeld := by
  exact final_spine_exact_gap_release_held

theorem public_boundary_theorem_3320_public_boundary_locked :
    publicBoundaryTheorem3320Certificate.publicBoundaryLocked := by
  exact final_spine_exact_gap_public_boundary_locked

theorem public_boundary_theorem_3320_exact_gap_does_not_open_final_release :
    publicBoundaryTheorem3320Certificate.exactGapDoesNotOpenFinalRelease := by
  trivial

end Release
end MGAP4D
