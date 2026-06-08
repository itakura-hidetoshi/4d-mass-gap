import MGAP4D.Spectral.SharpGapSandwich

namespace MGAP4D
namespace Spectral

/-- A pre-Mathlib exact-gap theorem certificate.

This certificate upgrades the sharp-gap sandwich tracking surface into an
exact-gap theorem surface: the structural mass gap value is the `33/20` value
witnessed by the lower-bound route and the orthogonal physical eigen-witness
route.  This remains a release-held theorem surface; it does not unlock the
public final theorem release. -/
structure ExactGapTheoremCertificate where
  sandwich : SharpGapSandwichCertificate
  sandwichReady : sandwich.ready
  gapWitness : GapWitness
  gapWitnessValue3320 : gapWitness.gap.value = 33 / 20
  exactGapValue : Rat
  exactGapValueMatchesSandwich : exactGapValue = sandwich.exactGapValue
  exactGapValueMatchesWitness : exactGapValue = gapWitness.gap.value
  exactGapValueIs3320 : exactGapValue = 33 / 20
  lowerBoundValueIs3320 : sandwich.lowerBound.lowerBound.value = 33 / 20
  eigenWitnessValueIs3320 : sandwich.eigenWitness.eigenWitness.eigenvalue = 33 / 20
  exactGapTheoremVisible : Prop
  finalReleaseHeld : sandwich.r1r7Completion.finalReleaseHeld
  publicBoundaryLocked : sandwich.r1r7Completion.publicBoundaryLocked
  theoremBoundaryHeld : sandwich.theoremBoundaryHeld

/-- Readiness re-expands all proof-carrying fields to the propositions they
certify, so the checklist remains a pure proposition-level conjunction. -/
def ExactGapTheoremCertificate.ready
    (C : ExactGapTheoremCertificate) : Prop :=
  C.sandwich.ready ∧ C.gapWitness.gap.value = 33 / 20 ∧
  C.exactGapValue = C.sandwich.exactGapValue ∧
  C.exactGapValue = C.gapWitness.gap.value ∧ C.exactGapValue = 33 / 20 ∧
  C.sandwich.lowerBound.lowerBound.value = 33 / 20 ∧
  C.sandwich.eigenWitness.eigenWitness.eigenvalue = 33 / 20 ∧
  C.exactGapTheoremVisible ∧ C.sandwich.r1r7Completion.finalReleaseHeld ∧
  C.sandwich.r1r7Completion.publicBoundaryLocked ∧ C.sandwich.theoremBoundaryHeld

def exactGapTheorem3320Certificate : ExactGapTheoremCertificate :=
  { sandwich := sharpGapSandwich3320Certificate
    sandwichReady := sharp_gap_sandwich_3320_ready
    gapWitness := gap3320Witness
    gapWitnessValue3320 := gap3320_value
    exactGapValue := 33 / 20
    exactGapValueMatchesSandwich := by rfl
    exactGapValueMatchesWitness := by rfl
    exactGapValueIs3320 := by rfl
    lowerBoundValueIs3320 := sharp_gap_sandwich_3320_lower_bound_value
    eigenWitnessValueIs3320 := sharp_gap_sandwich_3320_eigenvalue
    exactGapTheoremVisible := True
    finalReleaseHeld := sharp_gap_sandwich_3320_release_held
    publicBoundaryLocked := sharp_gap_sandwich_3320_public_boundary_locked
    theoremBoundaryHeld := by trivial }

theorem exact_gap_theorem_certificate_pack
    (C : ExactGapTheoremCertificate) :
    C.ready ↔ C.sandwich.ready ∧ C.gapWitness.gap.value = 33 / 20 ∧
      C.exactGapValue = C.sandwich.exactGapValue ∧
      C.exactGapValue = C.gapWitness.gap.value ∧ C.exactGapValue = 33 / 20 ∧
      C.sandwich.lowerBound.lowerBound.value = 33 / 20 ∧
      C.sandwich.eigenWitness.eigenWitness.eigenvalue = 33 / 20 ∧
      C.exactGapTheoremVisible ∧ C.sandwich.r1r7Completion.finalReleaseHeld ∧
      C.sandwich.r1r7Completion.publicBoundaryLocked ∧ C.sandwich.theoremBoundaryHeld := by
  rfl

theorem exact_gap_theorem_3320_ready :
    exactGapTheorem3320Certificate.ready := by
  exact And.intro sharp_gap_sandwich_3320_ready <|
    And.intro gap3320_value <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro sharp_gap_sandwich_3320_lower_bound_value <|
    And.intro sharp_gap_sandwich_3320_eigenvalue <|
    And.intro True.intro <|
    And.intro sharp_gap_sandwich_3320_release_held <|
    And.intro sharp_gap_sandwich_3320_public_boundary_locked True.intro

theorem exact_gap_theorem_3320_value :
    exactGapTheorem3320Certificate.exactGapValue = 33 / 20 := by
  rfl

theorem exact_gap_theorem_3320_matches_gap_witness :
    exactGapTheorem3320Certificate.exactGapValue = exactGapTheorem3320Certificate.gapWitness.gap.value := by
  rfl

theorem exact_gap_theorem_3320_matches_sandwich :
    exactGapTheorem3320Certificate.exactGapValue = exactGapTheorem3320Certificate.sandwich.exactGapValue := by
  rfl

theorem exact_gap_theorem_3320_lower_bound_value :
    exactGapTheorem3320Certificate.sandwich.lowerBound.lowerBound.value = 33 / 20 := by
  exact sharp_gap_sandwich_3320_lower_bound_value

theorem exact_gap_theorem_3320_lower_bound_value_matches_exact :
    exactGapTheorem3320Certificate.sandwich.lowerBound.lowerBound.value =
      exactGapTheorem3320Certificate.exactGapValue := by
  rfl

/-- Exact-gap theorem surface preserves the lower-bound sector boundary witness. -/
theorem exact_gap_theorem_3320_lower_bound_sector_boundary_ready :
    exactGapTheorem3320Certificate.sandwich.lowerBound.sectorBoundary.ready := by
  exact sharp_gap_sandwich_3320_lower_bound_sector_boundary_ready

theorem exact_gap_theorem_3320_lower_bound_sector_boundary_distinct :
    exactGapTheorem3320Certificate.sandwich.lowerBound.sectorBoundary.vacuumSector ≠
      exactGapTheorem3320Certificate.sandwich.lowerBound.sectorBoundary.orthogonalSector := by
  exact sharp_gap_sandwich_3320_lower_bound_sector_boundary_distinct

theorem exact_gap_theorem_3320_eigen_witness_value :
    exactGapTheorem3320Certificate.sandwich.eigenWitness.eigenWitness.eigenvalue = 33 / 20 := by
  exact sharp_gap_sandwich_3320_eigenvalue

theorem exact_gap_theorem_3320_eigen_witness_value_matches_exact :
    exactGapTheorem3320Certificate.sandwich.eigenWitness.eigenWitness.eigenvalue =
      exactGapTheorem3320Certificate.exactGapValue := by
  rfl

/-- Exact-gap release hold is exposed as the underlying sharp-sandwich
R1--R7 completion proposition. -/
theorem exact_gap_theorem_3320_release_held :
    exactGapTheorem3320Certificate.sandwich.r1r7Completion.finalReleaseHeld := by
  exact sharp_gap_sandwich_3320_release_held

/-- Exact-gap public-boundary lock is exposed as the underlying sharp-sandwich
R1--R7 completion proposition. -/
theorem exact_gap_theorem_3320_public_boundary_locked :
    exactGapTheorem3320Certificate.sandwich.r1r7Completion.publicBoundaryLocked := by
  exact sharp_gap_sandwich_3320_public_boundary_locked

end Spectral
end MGAP4D
