import MGAP4D.Spectral.PositiveGap
import MGAP4D.Spectral.SectorBoundary

namespace MGAP4D
namespace Spectral

/-- A pre-Mathlib certificate that the normalized `33/20` value is exposed as
the structural positive lower-bound surface for the current spectral-gap formalization. -/
structure LowerBoundCertificate where
  lowerBound : SpectralValue
  lowerBoundIs3320 : lowerBound.value = 33 / 20
  positiveGap : PositiveGapCertificate
  positiveGapMatchesLowerBound : positiveGap.value = lowerBound
  positiveGapNumeratorPositive : positiveGap.witness.gap.value.num > 0
  sectorBoundary : SectorBoundaryCertificate
  sectorBoundaryReady : sectorBoundary.ready
  positiveLowerBoundSurfaceVisible : Prop
  nonTheoremCompletionBoundaryVisible : Prop
  finalGapReleaseNotUnlocked : Prop
  mainPreMathlib : Prop

def LowerBoundCertificate.ready
    (C : LowerBoundCertificate) : Prop :=
  C.lowerBoundIs3320 ∧ C.positiveGapMatchesLowerBound ∧
  C.positiveGapNumeratorPositive ∧ C.sectorBoundaryReady ∧
  C.positiveLowerBoundSurfaceVisible ∧ C.nonTheoremCompletionBoundaryVisible ∧
  C.finalGapReleaseNotUnlocked ∧ C.mainPreMathlib

def lowerBound3320Certificate
    (positiveLowerBoundSurfaceVisible : Prop)
    (nonTheoremCompletionBoundaryVisible : Prop)
    (finalGapReleaseNotUnlocked : Prop)
    (mainPreMathlib : Prop) : LowerBoundCertificate :=
  { lowerBound := spectral3320
    lowerBoundIs3320 := by rfl
    positiveGap := positive3320GapCertificate
      positiveLowerBoundSurfaceVisible
      nonTheoremCompletionBoundaryVisible
      finalGapReleaseNotUnlocked
      mainPreMathlib
    positiveGapMatchesLowerBound := by rfl
    positiveGapNumeratorPositive := gap3320Witness.positiveNumerator
    sectorBoundary := spectralSectorBoundaryCertificate
      True True
      nonTheoremCompletionBoundaryVisible
      finalGapReleaseNotUnlocked
      mainPreMathlib
    sectorBoundaryReady := spectral_sector_boundary_certificate_ready
    positiveLowerBoundSurfaceVisible := positiveLowerBoundSurfaceVisible
    nonTheoremCompletionBoundaryVisible := nonTheoremCompletionBoundaryVisible
    finalGapReleaseNotUnlocked := finalGapReleaseNotUnlocked
    mainPreMathlib := mainPreMathlib }

theorem lower_bound_certificate_pack
    (C : LowerBoundCertificate) :
    C.ready ↔ C.lowerBoundIs3320 ∧ C.positiveGapMatchesLowerBound ∧
      C.positiveGapNumeratorPositive ∧ C.sectorBoundaryReady ∧
      C.positiveLowerBoundSurfaceVisible ∧ C.nonTheoremCompletionBoundaryVisible ∧
      C.finalGapReleaseNotUnlocked ∧ C.mainPreMathlib := by
  rfl

theorem lower_bound_3320_certificate_value :
    (lowerBound3320Certificate True True True True).lowerBound.value = 33 / 20 := by
  rfl

theorem lower_bound_3320_certificate_positive_numerator :
    (lowerBound3320Certificate True True True True).positiveGap.witness.gap.value.num > 0 := by
  exact gap3320Witness.positiveNumerator

theorem lower_bound_3320_certificate_ready :
    (lowerBound3320Certificate True True True True).ready := by
  exact And.intro rfl <|
    And.intro rfl <|
    And.intro gap3320Witness.positiveNumerator <|
    And.intro spectral_sector_boundary_certificate_ready <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

end Spectral
end MGAP4D
