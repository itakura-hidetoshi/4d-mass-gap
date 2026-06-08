import MGAP4D.Phase3ReleaseGate
import MGAP4D.Spectral.CoreCertificate

namespace MGAP4D

/-- A pre-Mathlib bridge from the spectral core certificate into the Phase 3
release-gate surface.

This bridge records visibility and readiness only. It is not final theorem
release and it does not claim R1--R7 theorem completion. -/
structure SpectralCoreReleaseBridge where
  coreCertificate : Spectral.SpectralCoreCertificate
  coreCertificateReady : coreCertificate.ready
  phase3ReleaseGateVisible : Prop
  spectralGapFormalizationGateVisible : Prop
  coreCertificateVisibleFromGate : Prop
  finalGapReleaseNotUnlocked : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  publicBoundaryHeld : Prop

/-- Readiness is a proposition-level checklist.  Proof-carrying fields are
re-expanded to their underlying propositions, rather than being reused as proof
terms inside the `∧` chain. -/
def SpectralCoreReleaseBridge.ready
    (B : SpectralCoreReleaseBridge) : Prop :=
  B.coreCertificate.ready ∧ B.phase3ReleaseGateVisible ∧
  B.spectralGapFormalizationGateVisible ∧ B.coreCertificateVisibleFromGate ∧
  B.finalGapReleaseNotUnlocked ∧ B.mainPreMathlib ∧
  B.mathlibMainAdoptionHeld ∧ B.publicBoundaryHeld

def spectral3320CoreReleaseBridge
    (phase3ReleaseGateVisible : Prop)
    (spectralGapFormalizationGateVisible : Prop)
    (coreCertificateVisibleFromGate : Prop)
    (finalGapReleaseNotUnlocked : Prop)
    (mainPreMathlib : Prop)
    (mathlibMainAdoptionHeld : Prop)
    (publicBoundaryHeld : Prop) : SpectralCoreReleaseBridge :=
  { coreCertificate := Spectral.spectral3320CoreCertificate
    coreCertificateReady := Spectral.spectral_3320_core_certificate_ready
    phase3ReleaseGateVisible := phase3ReleaseGateVisible
    spectralGapFormalizationGateVisible := spectralGapFormalizationGateVisible
    coreCertificateVisibleFromGate := coreCertificateVisibleFromGate
    finalGapReleaseNotUnlocked := finalGapReleaseNotUnlocked
    mainPreMathlib := mainPreMathlib
    mathlibMainAdoptionHeld := mathlibMainAdoptionHeld
    publicBoundaryHeld := publicBoundaryHeld }

theorem spectral_core_release_bridge_pack
    (B : SpectralCoreReleaseBridge) :
    B.ready ↔ B.coreCertificate.ready ∧ B.phase3ReleaseGateVisible ∧
      B.spectralGapFormalizationGateVisible ∧ B.coreCertificateVisibleFromGate ∧
      B.finalGapReleaseNotUnlocked ∧ B.mainPreMathlib ∧
      B.mathlibMainAdoptionHeld ∧ B.publicBoundaryHeld := by
  rfl

theorem spectral3320_core_release_bridge_ready :
    (spectral3320CoreReleaseBridge True True True True True True True).ready := by
  exact And.intro Spectral.spectral_3320_core_certificate_ready <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem spectral3320_core_release_bridge_value :
    (spectral3320CoreReleaseBridge True True True True True True True).coreCertificate.formalization.normalizedGapValue.value = 33 / 20 := by
  rfl

theorem spectral3320_core_release_bridge_positive_numerator :
    (spectral3320CoreReleaseBridge True True True True True True True).coreCertificate.lowerBound.positiveGap.witness.gap.value.num > 0 := by
  exact Spectral.gap3320Witness.positiveNumerator

end MGAP4D
