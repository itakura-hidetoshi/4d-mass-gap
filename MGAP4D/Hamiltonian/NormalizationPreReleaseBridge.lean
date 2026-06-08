import MGAP4D.Hamiltonian.SpectralNormalizationBridge
import MGAP4D.SpectralPreReleaseCheckpoint

namespace MGAP4D
namespace Hamiltonian

/-- A pre-Mathlib bridge from physical Hamiltonian normalization into the
spectral pre-release checkpoint.

This records that the normalized `H_phys` surface and the spectral pre-release
checkpoint share the same `33/20` gap value and positive witness while keeping
the public theorem boundary locked. -/
structure HamiltonianNormalizationPreReleaseBridge where
  hamiltonianSpectralBridge : HamiltonianSpectralNormalizationBridge
  hamiltonianSpectralBridgeReady : hamiltonianSpectralBridge.ready
  preReleaseCheckpoint : SpectralPreReleaseCheckpoint
  preReleaseCheckpointReady : preReleaseCheckpoint.ready
  normalizedGapMatchesCheckpoint :
    hamiltonianSpectralBridge.normalization.normalizedGap =
      preReleaseCheckpoint.lock.hold.closure.readiness.spine.bridge.coreCertificate.formalization.normalizedGapValue
  witnessMatchesCheckpoint :
    hamiltonianSpectralBridge.normalization.physicalGapRecord.witness =
      preReleaseCheckpoint.lock.hold.closure.readiness.spine.bridge.coreCertificate.formalization.witness
  unitScaleIsOne : hamiltonianSpectralBridge.normalization.unit.unitScale = 1
  vacuumReferenceIsZero : hamiltonianSpectralBridge.normalization.unit.vacuumEnergyReference = 0
  positiveNumeratorPreserved : hamiltonianSpectralBridge.normalization.physicalGapRecord.witness.gap.value.num > 0
  publicBoundaryLocked : preReleaseCheckpoint.publicBoundaryLocked
  bridgeVisible : Prop
  theoremBoundaryHeld : Prop

/-- Readiness is a proposition-level checklist.  Proof-carrying fields are
re-expanded to their underlying propositions, rather than being reused as proof
terms inside the `∧` chain. -/
def HamiltonianNormalizationPreReleaseBridge.ready
    (B : HamiltonianNormalizationPreReleaseBridge) : Prop :=
  B.hamiltonianSpectralBridge.ready ∧ B.preReleaseCheckpoint.ready ∧
  B.hamiltonianSpectralBridge.normalization.normalizedGap =
    B.preReleaseCheckpoint.lock.hold.closure.readiness.spine.bridge.coreCertificate.formalization.normalizedGapValue ∧
  B.hamiltonianSpectralBridge.normalization.physicalGapRecord.witness =
    B.preReleaseCheckpoint.lock.hold.closure.readiness.spine.bridge.coreCertificate.formalization.witness ∧
  B.hamiltonianSpectralBridge.normalization.unit.unitScale = 1 ∧
  B.hamiltonianSpectralBridge.normalization.unit.vacuumEnergyReference = 0 ∧
  B.hamiltonianSpectralBridge.normalization.physicalGapRecord.witness.gap.value.num > 0 ∧
  B.preReleaseCheckpoint.publicBoundaryLocked ∧ B.bridgeVisible ∧ B.theoremBoundaryHeld

def hamiltonian3320NormalizationPreReleaseBridge : HamiltonianNormalizationPreReleaseBridge :=
  { hamiltonianSpectralBridge := hamiltonianSpectral3320NormalizationBridge
    hamiltonianSpectralBridgeReady := hamiltonian_spectral_3320_normalization_bridge_ready
    preReleaseCheckpoint := spectral3320PreReleaseCheckpoint
    preReleaseCheckpointReady := spectral3320_pre_release_checkpoint_ready
    normalizedGapMatchesCheckpoint := by rfl
    witnessMatchesCheckpoint := by rfl
    unitScaleIsOne := by rfl
    vacuumReferenceIsZero := by rfl
    positiveNumeratorPreserved := Spectral.gap3320Witness.positiveNumerator
    publicBoundaryLocked := spectral3320_pre_release_checkpoint_boundary_locked
    bridgeVisible := True
    theoremBoundaryHeld := True }

theorem hamiltonian_normalization_pre_release_bridge_pack
    (B : HamiltonianNormalizationPreReleaseBridge) :
    B.ready ↔ B.hamiltonianSpectralBridge.ready ∧ B.preReleaseCheckpoint.ready ∧
      B.hamiltonianSpectralBridge.normalization.normalizedGap =
        B.preReleaseCheckpoint.lock.hold.closure.readiness.spine.bridge.coreCertificate.formalization.normalizedGapValue ∧
      B.hamiltonianSpectralBridge.normalization.physicalGapRecord.witness =
        B.preReleaseCheckpoint.lock.hold.closure.readiness.spine.bridge.coreCertificate.formalization.witness ∧
      B.hamiltonianSpectralBridge.normalization.unit.unitScale = 1 ∧
      B.hamiltonianSpectralBridge.normalization.unit.vacuumEnergyReference = 0 ∧
      B.hamiltonianSpectralBridge.normalization.physicalGapRecord.witness.gap.value.num > 0 ∧
      B.preReleaseCheckpoint.publicBoundaryLocked ∧ B.bridgeVisible ∧ B.theoremBoundaryHeld := by
  rfl

theorem hamiltonian3320_normalization_pre_release_bridge_ready :
    hamiltonian3320NormalizationPreReleaseBridge.ready := by
  exact And.intro hamiltonian_spectral_3320_normalization_bridge_ready <|
    And.intro spectral3320_pre_release_checkpoint_ready <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro Spectral.gap3320Witness.positiveNumerator <|
    And.intro spectral3320_pre_release_checkpoint_boundary_locked <|
    And.intro True.intro True.intro

theorem hamiltonian3320_pre_release_bridge_value :
    hamiltonian3320NormalizationPreReleaseBridge.hamiltonianSpectralBridge.normalization.normalizedGap.value = 33 / 20 := by
  rfl

theorem hamiltonian3320_pre_release_bridge_checkpoint_value :
    hamiltonian3320NormalizationPreReleaseBridge.preReleaseCheckpoint.lock.hold.closure.readiness.spine.bridge.coreCertificate.formalization.normalizedGapValue.value = 33 / 20 := by
  rfl

theorem hamiltonian3320_pre_release_bridge_preserves_positive_numerator :
    hamiltonian3320NormalizationPreReleaseBridge.hamiltonianSpectralBridge.normalization.physicalGapRecord.witness.gap.value.num > 0 := by
  exact Spectral.gap3320Witness.positiveNumerator

theorem hamiltonian3320_pre_release_bridge_public_boundary_locked :
    hamiltonian3320NormalizationPreReleaseBridge.preReleaseCheckpoint.publicBoundaryLocked := by
  exact spectral3320_pre_release_checkpoint_boundary_locked

end Hamiltonian
end MGAP4D
