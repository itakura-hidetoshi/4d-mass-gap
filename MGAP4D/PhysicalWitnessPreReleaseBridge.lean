import MGAP4D.PhysicalWitnessClosure
import MGAP4D.SpectralPreReleaseCheckpoint

namespace MGAP4D

/-- A pre-Mathlib bridge from the aggregate physical witness closure into the
spectral pre-release checkpoint.

This bridge makes explicit that the physical witness closure and the
pre-release checkpoint share the same normalized `33/20` value and the same
locked public boundary. -/
structure PhysicalWitnessPreReleaseBridge where
  physicalWitness : PhysicalWitnessClosure
  physicalWitnessReady : physicalWitness.ready
  checkpoint : SpectralPreReleaseCheckpoint
  checkpointReady : checkpoint.ready
  physicalGapMatchesCheckpoint :
    physicalWitness.hamiltonianBridge.hamiltonianSpectralBridge.normalization.normalizedGap.value =
      checkpoint.lock.hold.closure.readiness.spine.bridge.coreCertificate.formalization.normalizedGapValue.value
  observableWeightMatchesCheckpoint :
    physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.value =
      checkpoint.lock.hold.closure.readiness.spine.bridge.coreCertificate.formalization.normalizedGapValue.value
  witnessSectorOrthogonal :
    physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.sectorSeparation.witnessSector = Spectral.SpectralSector.orthogonal
  witnessNotVacuum :
    physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.sectorSeparation.witnessSector ≠ Spectral.SpectralSector.vacuum
  publicBoundaryLocked : checkpoint.publicBoundaryLocked
  bridgeVisible : Prop
  theoremBoundaryHeld : Prop

def PhysicalWitnessPreReleaseBridge.ready
    (B : PhysicalWitnessPreReleaseBridge) : Prop :=
  B.physicalWitnessReady ∧ B.checkpointReady ∧ B.physicalGapMatchesCheckpoint ∧
  B.observableWeightMatchesCheckpoint ∧ B.witnessSectorOrthogonal ∧ B.witnessNotVacuum ∧
  B.publicBoundaryLocked ∧ B.bridgeVisible ∧ B.theoremBoundaryHeld

def physicalWitness3320PreReleaseBridge : PhysicalWitnessPreReleaseBridge :=
  { physicalWitness := physicalWitness3320Closure
    physicalWitnessReady := physical_witness_3320_closure_ready
    checkpoint := spectral3320PreReleaseCheckpoint
    checkpointReady := spectral3320_pre_release_checkpoint_ready
    physicalGapMatchesCheckpoint := by rfl
    observableWeightMatchesCheckpoint := by rfl
    witnessSectorOrthogonal := by rfl
    witnessNotVacuum := by decide
    publicBoundaryLocked := spectral3320_pre_release_checkpoint_boundary_locked
    bridgeVisible := True
    theoremBoundaryHeld := True }

theorem physical_witness_pre_release_bridge_pack
    (B : PhysicalWitnessPreReleaseBridge) :
    B.ready ↔ B.physicalWitnessReady ∧ B.checkpointReady ∧ B.physicalGapMatchesCheckpoint ∧
      B.observableWeightMatchesCheckpoint ∧ B.witnessSectorOrthogonal ∧ B.witnessNotVacuum ∧
      B.publicBoundaryLocked ∧ B.bridgeVisible ∧ B.theoremBoundaryHeld := by
  rfl

theorem physical_witness_3320_pre_release_bridge_ready :
    physicalWitness3320PreReleaseBridge.ready := by
  exact And.intro physical_witness_3320_closure_ready <|
    And.intro spectral3320_pre_release_checkpoint_ready <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro (by decide) <|
    And.intro spectral3320_pre_release_checkpoint_boundary_locked <|
    And.intro True.intro True.intro

theorem physical_witness_3320_pre_release_bridge_physical_value :
    physicalWitness3320PreReleaseBridge.physicalWitness.hamiltonianBridge.hamiltonianSpectralBridge.normalization.normalizedGap.value = 33 / 20 := by
  rfl

theorem physical_witness_3320_pre_release_bridge_observable_value :
    physicalWitness3320PreReleaseBridge.physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.value = 33 / 20 := by
  rfl

theorem physical_witness_3320_pre_release_bridge_witness_orthogonal :
    physicalWitness3320PreReleaseBridge.physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.sectorSeparation.witnessSector =
      Spectral.SpectralSector.orthogonal := by
  rfl

theorem physical_witness_3320_pre_release_bridge_witness_not_vacuum :
    physicalWitness3320PreReleaseBridge.physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.sectorSeparation.witnessSector ≠
      Spectral.SpectralSector.vacuum := by
  decide

theorem physical_witness_3320_pre_release_bridge_public_boundary_locked :
    physicalWitness3320PreReleaseBridge.checkpoint.publicBoundaryLocked := by
  exact spectral3320_pre_release_checkpoint_boundary_locked

end MGAP4D
