import MGAP4D.Spectral.GapFormalization

namespace MGAP4D
namespace Spectral

/-- A pre-Mathlib certificate that the normalized spectral-gap surface carries
an explicitly positive witness.  This remains a structural proof-surface: it
records the positivity evidence already present in `GapWitness` without
claiming final theorem release. -/
structure PositiveGapCertificate where
  value : SpectralValue
  valueIs3320 : value.value = 33 / 20
  witness : GapWitness
  witnessMatchesValue : witness.gap = value
  witnessPositiveNumerator : witness.gap.value.num > 0
  positiveLowerBoundSurfaceVisible : Prop
  nonTheoremCompletionBoundaryVisible : Prop
  finalGapReleaseNotUnlocked : Prop
  mainPreMathlib : Prop

/-- Readiness is a proposition-level checklist.  Proof-carrying fields are
re-expanded to their underlying propositions, rather than being reused as proof
terms inside the `∧` chain. -/
def PositiveGapCertificate.ready
    (C : PositiveGapCertificate) : Prop :=
  C.value.value = 33 / 20 ∧ C.witness.gap = C.value ∧
  C.witness.gap.value.num > 0 ∧ C.positiveLowerBoundSurfaceVisible ∧
  C.nonTheoremCompletionBoundaryVisible ∧ C.finalGapReleaseNotUnlocked ∧
  C.mainPreMathlib

def positive3320GapCertificate
    (positiveLowerBoundSurfaceVisible : Prop)
    (nonTheoremCompletionBoundaryVisible : Prop)
    (finalGapReleaseNotUnlocked : Prop)
    (mainPreMathlib : Prop) : PositiveGapCertificate :=
  { value := spectral3320
    valueIs3320 := by rfl
    witness := gap3320Witness
    witnessMatchesValue := by rfl
    witnessPositiveNumerator := gap3320Witness.positiveNumerator
    positiveLowerBoundSurfaceVisible := positiveLowerBoundSurfaceVisible
    nonTheoremCompletionBoundaryVisible := nonTheoremCompletionBoundaryVisible
    finalGapReleaseNotUnlocked := finalGapReleaseNotUnlocked
    mainPreMathlib := mainPreMathlib }

theorem positive_gap_certificate_pack
    (C : PositiveGapCertificate) :
    C.ready ↔ C.value.value = 33 / 20 ∧ C.witness.gap = C.value ∧
      C.witness.gap.value.num > 0 ∧ C.positiveLowerBoundSurfaceVisible ∧
      C.nonTheoremCompletionBoundaryVisible ∧ C.finalGapReleaseNotUnlocked ∧
      C.mainPreMathlib := by
  rfl

theorem positive3320_gap_certificate_ready :
    (positive3320GapCertificate True True True True).ready := by
  exact ⟨rfl, rfl, gap3320Witness.positiveNumerator,
    True.intro, True.intro, True.intro, True.intro⟩

theorem positive3320_gap_certificate_value :
    (positive3320GapCertificate True True True True).value.value = 33 / 20 := by
  rfl

theorem positive3320_gap_certificate_positive_numerator :
    (positive3320GapCertificate True True True True).witness.gap.value.num > 0 := by
  exact gap3320Witness.positiveNumerator

/-- Connect the positive-gap certificate back to the earlier formalization
surface by sharing the same normalized `33/20` carrier. -/
theorem positive3320_certificate_matches_formalization_value :
    (positive3320GapCertificate True True True True).value =
      (spectralGap3320Formalization True True True True True True True True).normalizedGapValue := by
  rfl

end Spectral
end MGAP4D
