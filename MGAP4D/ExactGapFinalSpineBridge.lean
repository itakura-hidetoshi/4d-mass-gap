import MGAP4D.FinalSpine
import MGAP4D.Spectral.ExactGapTheorem

namespace MGAP4D

/-- A pre-Mathlib bridge exposing the exact-gap theorem certificate from the
final spine.

This bridge records that the final spine sees the exact-gap theorem surface:
`m_gap` tracking value `33/20`, matched with the gap witness and sharp-gap
sandwich, while final public release remains held. -/
structure ExactGapFinalSpineBridge where
  exactGap : Spectral.ExactGapTheoremCertificate
  exactGapReady : exactGap.ready
  exactGapValue3320 : exactGap.exactGapValue = 33 / 20
  exactGapMatchesWitness : exactGap.exactGapValue = exactGap.gapWitness.gap.value
  exactGapMatchesSandwich : exactGap.exactGapValue = exactGap.sandwich.exactGapValue
  lowerBoundValue3320 : exactGap.sandwich.lowerBound.lowerBound.value = 33 / 20
  eigenWitnessValue3320 : exactGap.sandwich.eigenWitness.eigenWitness.eigenvalue = 33 / 20
  finalReleaseHeld : exactGap.finalReleaseHeld
  publicBoundaryLocked : exactGap.publicBoundaryLocked
  finalSpineBridgeVisible : Prop
  theoremBoundaryHeld : exactGap.theoremBoundaryHeld

def ExactGapFinalSpineBridge.ready
    (B : ExactGapFinalSpineBridge) : Prop :=
  B.exactGapReady ∧ B.exactGapValue3320 ∧ B.exactGapMatchesWitness ∧
  B.exactGapMatchesSandwich ∧ B.lowerBoundValue3320 ∧ B.eigenWitnessValue3320 ∧
  B.finalReleaseHeld ∧ B.publicBoundaryLocked ∧ B.finalSpineBridgeVisible ∧
  B.theoremBoundaryHeld

def exactGapFinalSpineBridge3320 : ExactGapFinalSpineBridge :=
  { exactGap := Spectral.exactGapTheorem3320Certificate
    exactGapReady := Spectral.exact_gap_theorem_3320_ready
    exactGapValue3320 := Spectral.exact_gap_theorem_3320_value
    exactGapMatchesWitness := Spectral.exact_gap_theorem_3320_matches_gap_witness
    exactGapMatchesSandwich := Spectral.exact_gap_theorem_3320_matches_sandwich
    lowerBoundValue3320 := Spectral.exact_gap_theorem_3320_lower_bound_value
    eigenWitnessValue3320 := Spectral.exact_gap_theorem_3320_eigen_witness_value
    finalReleaseHeld := Spectral.exact_gap_theorem_3320_release_held
    publicBoundaryLocked := Spectral.exact_gap_theorem_3320_public_boundary_locked
    finalSpineBridgeVisible := True
    theoremBoundaryHeld := by trivial }

theorem exact_gap_final_spine_bridge_pack
    (B : ExactGapFinalSpineBridge) :
    B.ready ↔ B.exactGapReady ∧ B.exactGapValue3320 ∧ B.exactGapMatchesWitness ∧
      B.exactGapMatchesSandwich ∧ B.lowerBoundValue3320 ∧ B.eigenWitnessValue3320 ∧
      B.finalReleaseHeld ∧ B.publicBoundaryLocked ∧ B.finalSpineBridgeVisible ∧
      B.theoremBoundaryHeld := by
  rfl

theorem exact_gap_final_spine_bridge_3320_ready :
    exactGapFinalSpineBridge3320.ready := by
  exact And.intro Spectral.exact_gap_theorem_3320_ready <|
    And.intro Spectral.exact_gap_theorem_3320_value <|
    And.intro Spectral.exact_gap_theorem_3320_matches_gap_witness <|
    And.intro Spectral.exact_gap_theorem_3320_matches_sandwich <|
    And.intro Spectral.exact_gap_theorem_3320_lower_bound_value <|
    And.intro Spectral.exact_gap_theorem_3320_eigen_witness_value <|
    And.intro Spectral.exact_gap_theorem_3320_release_held <|
    And.intro Spectral.exact_gap_theorem_3320_public_boundary_locked <|
    And.intro True.intro True.intro

theorem final_spine_exact_gap_theorem_ready :
    Spectral.exactGapTheorem3320Certificate.ready := by
  exact Spectral.exact_gap_theorem_3320_ready

theorem final_spine_exact_gap_value_3320 :
    Spectral.exactGapTheorem3320Certificate.exactGapValue = 33 / 20 := by
  exact Spectral.exact_gap_theorem_3320_value

theorem final_spine_exact_gap_matches_gap_witness :
    Spectral.exactGapTheorem3320Certificate.exactGapValue =
      Spectral.exactGapTheorem3320Certificate.gapWitness.gap.value := by
  exact Spectral.exact_gap_theorem_3320_matches_gap_witness

theorem final_spine_exact_gap_matches_sandwich :
    Spectral.exactGapTheorem3320Certificate.exactGapValue =
      Spectral.exactGapTheorem3320Certificate.sandwich.exactGapValue := by
  exact Spectral.exact_gap_theorem_3320_matches_sandwich

theorem final_spine_exact_gap_release_held :
    Spectral.exactGapTheorem3320Certificate.finalReleaseHeld := by
  exact Spectral.exact_gap_theorem_3320_release_held

theorem final_spine_exact_gap_public_boundary_locked :
    Spectral.exactGapTheorem3320Certificate.publicBoundaryLocked := by
  exact Spectral.exact_gap_theorem_3320_public_boundary_locked

end MGAP4D
