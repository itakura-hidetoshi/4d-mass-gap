import MGAP4D.Spectral.GapFormalization
import MGAP4D.Spectral.LowerBound

namespace MGAP4D
namespace Spectral

/-- A pre-Mathlib core certificate bundling the current spectral-gap
formalization surface, the lower-bound certificate, the positive witness, and
sector-boundary readiness. -/
structure SpectralCoreCertificate where
  formalization : SpectralGapFormalization
  formalizationReady : formalization.ready
  lowerBound : LowerBoundCertificate
  lowerBoundReady : lowerBound.ready
  formalizationMatchesLowerBound : formalization.normalizedGapValue = lowerBound.lowerBound
  witnessMatchesLowerBoundWitness : formalization.witness = lowerBound.positiveGap.witness
  sectorBoundaryReady : lowerBound.sectorBoundary.ready
  coreCertificateVisible : Prop
  nonTheoremCompletionBoundaryVisible : Prop
  finalGapReleaseNotUnlocked : Prop
  mainPreMathlib : Prop

def SpectralCoreCertificate.ready
    (C : SpectralCoreCertificate) : Prop :=
  C.formalizationReady ∧ C.lowerBoundReady ∧ C.formalizationMatchesLowerBound ∧
  C.witnessMatchesLowerBoundWitness ∧ C.sectorBoundaryReady ∧
  C.coreCertificateVisible ∧ C.nonTheoremCompletionBoundaryVisible ∧
  C.finalGapReleaseNotUnlocked ∧ C.mainPreMathlib

theorem spectral_gap_3320_formalization_ready :
    (spectralGap3320Formalization True True True True True True True True).ready := by
  exact And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro rfl <|
    And.intro True.intro <|
    And.intro rfl <|
    And.intro True.intro <|
    And.intro True.intro True.intro

def spectral3320CoreCertificate : SpectralCoreCertificate :=
  { formalization := spectralGap3320Formalization True True True True True True True True
    formalizationReady := spectral_gap_3320_formalization_ready
    lowerBound := lowerBound3320Certificate True True True True
    lowerBoundReady := lower_bound_3320_certificate_ready
    formalizationMatchesLowerBound := by rfl
    witnessMatchesLowerBoundWitness := by rfl
    sectorBoundaryReady := spectral_sector_boundary_certificate_ready
    coreCertificateVisible := True
    nonTheoremCompletionBoundaryVisible := True
    finalGapReleaseNotUnlocked := True
    mainPreMathlib := True }

theorem spectral_core_certificate_pack
    (C : SpectralCoreCertificate) :
    C.ready ↔ C.formalizationReady ∧ C.lowerBoundReady ∧
      C.formalizationMatchesLowerBound ∧ C.witnessMatchesLowerBoundWitness ∧
      C.sectorBoundaryReady ∧ C.coreCertificateVisible ∧
      C.nonTheoremCompletionBoundaryVisible ∧ C.finalGapReleaseNotUnlocked ∧
      C.mainPreMathlib := by
  rfl

theorem spectral_3320_core_certificate_ready :
    spectral3320CoreCertificate.ready := by
  exact And.intro spectral_gap_3320_formalization_ready <|
    And.intro lower_bound_3320_certificate_ready <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro spectral_sector_boundary_certificate_ready <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem spectral_3320_core_certificate_value :
    spectral3320CoreCertificate.formalization.normalizedGapValue.value = 33 / 20 := by
  rfl

theorem spectral_3320_core_certificate_lower_bound_value :
    spectral3320CoreCertificate.lowerBound.lowerBound.value = 33 / 20 := by
  rfl

theorem spectral_3320_core_certificate_positive_numerator :
    spectral3320CoreCertificate.lowerBound.positiveGap.witness.gap.value.num > 0 := by
  exact gap3320Witness.positiveNumerator

end Spectral
end MGAP4D
