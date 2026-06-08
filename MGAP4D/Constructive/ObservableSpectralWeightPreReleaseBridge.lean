import MGAP4D.Constructive.ObservableSpectralWeightBridge
import MGAP4D.SpectralPreReleaseCheckpoint

namespace MGAP4D
namespace Constructive

/-- A pre-Mathlib bridge from observable spectral weight into the spectral
pre-release checkpoint.

This records that the `A_{p,g}` positive spectral-weight witness used by the
constructive final packet is aligned with the review-gated pre-release
checkpoint while the public theorem boundary remains locked. -/
structure ObservableSpectralWeightPreReleaseBridge where
  finalBridge : ObservableSpectralWeightFinalBridge
  finalBridgeReady : finalBridge.ready
  preReleaseCheckpoint : SpectralPreReleaseCheckpoint
  preReleaseCheckpointReady : preReleaseCheckpoint.ready
  finalMassMatchesCheckpoint :
    finalBridge.finalPacket.massGap.value =
      preReleaseCheckpoint.lock.hold.closure.readiness.spine.bridge.coreCertificate.formalization.normalizedGapValue.value
  spectralWeightValueMatchesCheckpoint :
    finalBridge.spectralWeight.value =
      preReleaseCheckpoint.lock.hold.closure.readiness.spine.bridge.coreCertificate.formalization.normalizedGapValue.value
  finalPlaquettePositive : finalBridge.finalPacket.plaquette.observableWitness.positiveMass = true
  observableWeightPositive : finalBridge.spectralWeight.massWitness.positiveMass = true
  witnessSectorOrthogonal : finalBridge.spectralWeight.sectorSeparation.witnessSector = Spectral.SpectralSector.orthogonal
  witnessNotVacuum : finalBridge.spectralWeight.sectorSeparation.witnessSector ≠ Spectral.SpectralSector.vacuum
  publicBoundaryLocked : preReleaseCheckpoint.publicBoundaryLocked
  bridgeVisible : Prop
  theoremBoundaryHeld : Prop

/-- Readiness is a proposition-level checklist.  Proof-carrying fields are
re-expanded to their underlying propositions, rather than being reused as proof
terms inside the `∧` chain. -/
def ObservableSpectralWeightPreReleaseBridge.ready
    (B : ObservableSpectralWeightPreReleaseBridge) : Prop :=
  B.finalBridge.ready ∧ B.preReleaseCheckpoint.ready ∧
  B.finalBridge.finalPacket.massGap.value =
    B.preReleaseCheckpoint.lock.hold.closure.readiness.spine.bridge.coreCertificate.formalization.normalizedGapValue.value ∧
  B.finalBridge.spectralWeight.value =
    B.preReleaseCheckpoint.lock.hold.closure.readiness.spine.bridge.coreCertificate.formalization.normalizedGapValue.value ∧
  B.finalBridge.finalPacket.plaquette.observableWitness.positiveMass = true ∧
  B.finalBridge.spectralWeight.massWitness.positiveMass = true ∧
  B.finalBridge.spectralWeight.sectorSeparation.witnessSector = Spectral.SpectralSector.orthogonal ∧
  B.finalBridge.spectralWeight.sectorSeparation.witnessSector ≠ Spectral.SpectralSector.vacuum ∧
  B.preReleaseCheckpoint.publicBoundaryLocked ∧ B.bridgeVisible ∧ B.theoremBoundaryHeld

def observableSpectralWeight3320PreReleaseBridge : ObservableSpectralWeightPreReleaseBridge :=
  { finalBridge := observableSpectralWeight3320FinalBridge
    finalBridgeReady := observable_spectral_weight_3320_final_bridge_ready
    preReleaseCheckpoint := spectral3320PreReleaseCheckpoint
    preReleaseCheckpointReady := spectral3320_pre_release_checkpoint_ready
    finalMassMatchesCheckpoint := by rfl
    spectralWeightValueMatchesCheckpoint := by rfl
    finalPlaquettePositive := by rfl
    observableWeightPositive := by rfl
    witnessSectorOrthogonal := by rfl
    witnessNotVacuum := by decide
    publicBoundaryLocked := spectral3320_pre_release_checkpoint_boundary_locked
    bridgeVisible := True
    theoremBoundaryHeld := True }

theorem observable_spectral_weight_pre_release_bridge_pack
    (B : ObservableSpectralWeightPreReleaseBridge) :
    B.ready ↔ B.finalBridge.ready ∧ B.preReleaseCheckpoint.ready ∧
      B.finalBridge.finalPacket.massGap.value =
        B.preReleaseCheckpoint.lock.hold.closure.readiness.spine.bridge.coreCertificate.formalization.normalizedGapValue.value ∧
      B.finalBridge.spectralWeight.value =
        B.preReleaseCheckpoint.lock.hold.closure.readiness.spine.bridge.coreCertificate.formalization.normalizedGapValue.value ∧
      B.finalBridge.finalPacket.plaquette.observableWitness.positiveMass = true ∧
      B.finalBridge.spectralWeight.massWitness.positiveMass = true ∧
      B.finalBridge.spectralWeight.sectorSeparation.witnessSector = Spectral.SpectralSector.orthogonal ∧
      B.finalBridge.spectralWeight.sectorSeparation.witnessSector ≠ Spectral.SpectralSector.vacuum ∧
      B.preReleaseCheckpoint.publicBoundaryLocked ∧ B.bridgeVisible ∧ B.theoremBoundaryHeld := by
  rfl

theorem observable_spectral_weight_3320_pre_release_bridge_ready :
    observableSpectralWeight3320PreReleaseBridge.ready := by
  exact And.intro observable_spectral_weight_3320_final_bridge_ready <|
    And.intro spectral3320_pre_release_checkpoint_ready <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro (by decide) <|
    And.intro spectral3320_pre_release_checkpoint_boundary_locked <|
    And.intro True.intro True.intro

theorem observable_spectral_weight_3320_pre_release_bridge_final_mass_value :
    observableSpectralWeight3320PreReleaseBridge.finalBridge.finalPacket.massGap.value = 33 / 20 := by
  rfl

theorem observable_spectral_weight_3320_pre_release_bridge_weight_value :
    observableSpectralWeight3320PreReleaseBridge.finalBridge.spectralWeight.value = 33 / 20 := by
  rfl

theorem observable_spectral_weight_3320_pre_release_bridge_positive_mass :
    observableSpectralWeight3320PreReleaseBridge.finalBridge.spectralWeight.massWitness.positiveMass = true := by
  rfl

theorem observable_spectral_weight_3320_pre_release_bridge_witness_orthogonal :
    observableSpectralWeight3320PreReleaseBridge.finalBridge.spectralWeight.sectorSeparation.witnessSector =
      Spectral.SpectralSector.orthogonal := by
  rfl

theorem observable_spectral_weight_3320_pre_release_bridge_witness_not_vacuum :
    observableSpectralWeight3320PreReleaseBridge.finalBridge.spectralWeight.sectorSeparation.witnessSector ≠
      Spectral.SpectralSector.vacuum := by
  decide

theorem observable_spectral_weight_3320_pre_release_bridge_public_boundary_locked :
    observableSpectralWeight3320PreReleaseBridge.preReleaseCheckpoint.publicBoundaryLocked := by
  exact spectral3320_pre_release_checkpoint_boundary_locked

end Constructive
end MGAP4D
