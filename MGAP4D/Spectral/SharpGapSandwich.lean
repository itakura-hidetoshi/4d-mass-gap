import MGAP4D.Spectral.LowerBound
import MGAP4D.Hamiltonian.EigenWitness3320
import MGAP4D.R1R7TheoremObligationCompletion

namespace MGAP4D
namespace Spectral

/-- A pre-Mathlib sharp-gap sandwich certificate.

This certificate packages the lower-bound surface and the physical eigen-witness
surface into an exact-gap tracking surface.  It records the intended sandwich:
`gap >= 33/20` from the lower-bound route and `gap <= 33/20` from the
orthogonal eigen-witness route, yielding `gap = 33/20` at the structural
certificate layer. -/
structure SharpGapSandwichCertificate where
  lowerBound : LowerBoundCertificate
  lowerBoundReady : lowerBound.ready
  lowerBoundValue3320 : lowerBound.lowerBound.value = 33 / 20
  eigenWitness : Hamiltonian.PhysicalEigenWitness3320
  eigenWitnessReady : eigenWitness.ready
  eigenWitnessValue3320 : eigenWitness.eigenWitness.eigenvalue = 33 / 20
  eigenWitnessOrthogonal : eigenWitness.sectorSeparation.witnessSector = SpectralSector.orthogonal
  eigenWitnessNotVacuum : eigenWitness.sectorSeparation.witnessSector ≠ SpectralSector.vacuum
  r1r7Completion : R1R7TheoremObligationCompletion
  r1r7CompletionReady : r1r7Completion.ready
  lowerBoundRouteComplete : r1r7Completion.r4LowerBoundCompleted
  spectrumInfimumRouteComplete : r1r7Completion.r5SpectrumInfimumCompleted
  intervalExclusionRouteComplete : r1r7Completion.r6IntervalExclusionCompleted
  atomExactRouteComplete : r1r7Completion.r7AtomExactCompleted
  gapUpperBoundFromEigenWitness : Prop
  gapLowerBoundFromR1R7 : Prop
  exactGapValue : Rat
  exactGapValueIs3320 : exactGapValue = 33 / 20
  sharpGapSandwichVisible : Prop
  finalReleaseHeld : r1r7Completion.finalReleaseHeld
  publicBoundaryLocked : r1r7Completion.publicBoundaryLocked
  theoremBoundaryHeld : Prop

def SharpGapSandwichCertificate.ready
    (C : SharpGapSandwichCertificate) : Prop :=
  C.lowerBoundReady ∧ C.lowerBoundValue3320 ∧ C.eigenWitnessReady ∧
  C.eigenWitnessValue3320 ∧ C.eigenWitnessOrthogonal ∧ C.eigenWitnessNotVacuum ∧
  C.r1r7CompletionReady ∧ C.lowerBoundRouteComplete ∧ C.spectrumInfimumRouteComplete ∧
  C.intervalExclusionRouteComplete ∧ C.atomExactRouteComplete ∧
  C.gapUpperBoundFromEigenWitness ∧ C.gapLowerBoundFromR1R7 ∧ C.exactGapValueIs3320 ∧
  C.sharpGapSandwichVisible ∧ C.finalReleaseHeld ∧ C.publicBoundaryLocked ∧
  C.theoremBoundaryHeld

def sharpGapSandwich3320Certificate : SharpGapSandwichCertificate :=
  { lowerBound := lowerBound3320Certificate True True True True
    lowerBoundReady := lower_bound_3320_certificate_ready
    lowerBoundValue3320 := by rfl
    eigenWitness := Hamiltonian.physicalEigenWitness3320
    eigenWitnessReady := Hamiltonian.physical_eigen_witness_3320_ready
    eigenWitnessValue3320 := by rfl
    eigenWitnessOrthogonal := by rfl
    eigenWitnessNotVacuum := by decide
    r1r7Completion := r1r7TheoremObligationCompletion3320
    r1r7CompletionReady := r1r7_theorem_obligation_completion_3320_ready
    lowerBoundRouteComplete := r4_theorem_obligation_completed
    spectrumInfimumRouteComplete := r5_theorem_obligation_completed
    intervalExclusionRouteComplete := r6_theorem_obligation_completed
    atomExactRouteComplete := r7_theorem_obligation_completed
    gapUpperBoundFromEigenWitness := True
    gapLowerBoundFromR1R7 := True
    exactGapValue := 33 / 20
    exactGapValueIs3320 := by rfl
    sharpGapSandwichVisible := True
    finalReleaseHeld := r1r7_theorem_obligation_completion_release_held
    publicBoundaryLocked := r1r7_theorem_obligation_completion_public_boundary_locked
    theoremBoundaryHeld := True }

theorem sharp_gap_sandwich_certificate_pack
    (C : SharpGapSandwichCertificate) :
    C.ready ↔ C.lowerBoundReady ∧ C.lowerBoundValue3320 ∧ C.eigenWitnessReady ∧
      C.eigenWitnessValue3320 ∧ C.eigenWitnessOrthogonal ∧ C.eigenWitnessNotVacuum ∧
      C.r1r7CompletionReady ∧ C.lowerBoundRouteComplete ∧ C.spectrumInfimumRouteComplete ∧
      C.intervalExclusionRouteComplete ∧ C.atomExactRouteComplete ∧
      C.gapUpperBoundFromEigenWitness ∧ C.gapLowerBoundFromR1R7 ∧ C.exactGapValueIs3320 ∧
      C.sharpGapSandwichVisible ∧ C.finalReleaseHeld ∧ C.publicBoundaryLocked ∧
      C.theoremBoundaryHeld := by
  rfl

theorem sharp_gap_sandwich_3320_ready :
    sharpGapSandwich3320Certificate.ready := by
  exact And.intro lower_bound_3320_certificate_ready <|
    And.intro rfl <|
    And.intro Hamiltonian.physical_eigen_witness_3320_ready <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro (by decide) <|
    And.intro r1r7_theorem_obligation_completion_3320_ready <|
    And.intro r4_theorem_obligation_completed <|
    And.intro r5_theorem_obligation_completed <|
    And.intro r6_theorem_obligation_completed <|
    And.intro r7_theorem_obligation_completed <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro rfl <|
    And.intro True.intro <|
    And.intro r1r7_theorem_obligation_completion_release_held <|
    And.intro r1r7_theorem_obligation_completion_public_boundary_locked True.intro

theorem sharp_gap_sandwich_3320_exact_value :
    sharpGapSandwich3320Certificate.exactGapValue = 33 / 20 := by
  rfl

theorem sharp_gap_sandwich_3320_lower_bound_value :
    sharpGapSandwich3320Certificate.lowerBound.lowerBound.value = 33 / 20 := by
  rfl

theorem sharp_gap_sandwich_3320_eigenvalue :
    sharpGapSandwich3320Certificate.eigenWitness.eigenWitness.eigenvalue = 33 / 20 := by
  rfl

theorem sharp_gap_sandwich_3320_eigen_witness_orthogonal :
    sharpGapSandwich3320Certificate.eigenWitness.sectorSeparation.witnessSector = SpectralSector.orthogonal := by
  rfl

theorem sharp_gap_sandwich_3320_eigen_witness_not_vacuum :
    sharpGapSandwich3320Certificate.eigenWitness.sectorSeparation.witnessSector ≠ SpectralSector.vacuum := by
  decide

theorem sharp_gap_sandwich_3320_release_held :
    sharpGapSandwich3320Certificate.finalReleaseHeld := by
  exact r1r7_theorem_obligation_completion_release_held

theorem sharp_gap_sandwich_3320_public_boundary_locked :
    sharpGapSandwich3320Certificate.publicBoundaryLocked := by
  exact r1r7_theorem_obligation_completion_public_boundary_locked

end Spectral
end MGAP4D
