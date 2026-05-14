import MGAP4D.PhysicalWitnessPreReleaseBridge
import MGAP4D.SpectralPublicBoundaryLock

namespace MGAP4D

/-- A pre-Mathlib release-hold layer for the aggregate physical witness spine.

The physical witness is visible through `H_phys`, the `A_pg` observable, the
`33/20` normalized value, and the orthogonal-sector witness.  This hold layer
records that these visible surfaces do not open final theorem release. -/
structure PhysicalWitnessReleaseHold where
  bridge : PhysicalWitnessPreReleaseBridge
  bridgeReady : bridge.ready
  publicBoundaryLock : SpectralPublicBoundaryLock
  publicBoundaryLockReady : publicBoundaryLock.ready
  physicalValueVisible : bridge.physicalWitness.hamiltonianBridge.hamiltonianSpectralBridge.normalization.normalizedGap.value = 33 / 20
  observableWeightVisible : bridge.physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.value = 33 / 20
  observableIsApg : bridge.physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.observable = Plaquette.A_pg
  positiveObservableMass : bridge.physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.massWitness.positiveMass = true
  witnessSectorOrthogonal : bridge.physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.sectorSeparation.witnessSector = Spectral.SpectralSector.orthogonal
  witnessNotVacuum : bridge.physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.sectorSeparation.witnessSector ≠ Spectral.SpectralSector.vacuum
  publicBoundaryLocked : bridge.checkpoint.publicBoundaryLocked
  finalReleaseHeld : Prop
  theoremCompletionsNotClaimed : Prop
  theoremBoundaryHeld : Prop

def PhysicalWitnessReleaseHold.ready
    (H : PhysicalWitnessReleaseHold) : Prop :=
  H.bridgeReady ∧ H.publicBoundaryLockReady ∧ H.physicalValueVisible ∧
  H.observableWeightVisible ∧ H.observableIsApg ∧ H.positiveObservableMass ∧
  H.witnessSectorOrthogonal ∧ H.witnessNotVacuum ∧ H.publicBoundaryLocked ∧
  H.finalReleaseHeld ∧ H.theoremCompletionsNotClaimed ∧ H.theoremBoundaryHeld

def physicalWitness3320ReleaseHold : PhysicalWitnessReleaseHold :=
  { bridge := physicalWitness3320PreReleaseBridge
    bridgeReady := physical_witness_3320_pre_release_bridge_ready
    publicBoundaryLock := spectral3320PublicBoundaryLock
    publicBoundaryLockReady := spectral3320_public_boundary_lock_ready
    physicalValueVisible := by rfl
    observableWeightVisible := by rfl
    observableIsApg := by rfl
    positiveObservableMass := by rfl
    witnessSectorOrthogonal := by rfl
    witnessNotVacuum := by decide
    publicBoundaryLocked := spectral3320_pre_release_checkpoint_boundary_locked
    finalReleaseHeld := True
    theoremCompletionsNotClaimed := True
    theoremBoundaryHeld := True }

theorem physical_witness_release_hold_pack
    (H : PhysicalWitnessReleaseHold) :
    H.ready ↔ H.bridgeReady ∧ H.publicBoundaryLockReady ∧ H.physicalValueVisible ∧
      H.observableWeightVisible ∧ H.observableIsApg ∧ H.positiveObservableMass ∧
      H.witnessSectorOrthogonal ∧ H.witnessNotVacuum ∧ H.publicBoundaryLocked ∧
      H.finalReleaseHeld ∧ H.theoremCompletionsNotClaimed ∧ H.theoremBoundaryHeld := by
  rfl

theorem physical_witness_3320_release_hold_ready :
    physicalWitness3320ReleaseHold.ready := by
  exact And.intro physical_witness_3320_pre_release_bridge_ready <|
    And.intro spectral3320_public_boundary_lock_ready <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro (by decide) <|
    And.intro spectral3320_pre_release_checkpoint_boundary_locked <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem physical_witness_3320_release_hold_physical_value :
    physicalWitness3320ReleaseHold.bridge.physicalWitness.hamiltonianBridge.hamiltonianSpectralBridge.normalization.normalizedGap.value = 33 / 20 := by
  rfl

theorem physical_witness_3320_release_hold_observable_value :
    physicalWitness3320ReleaseHold.bridge.physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.value = 33 / 20 := by
  rfl

theorem physical_witness_3320_release_hold_observable_Apg :
    physicalWitness3320ReleaseHold.bridge.physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.observable = Plaquette.A_pg := by
  rfl

theorem physical_witness_3320_release_hold_positive_mass :
    physicalWitness3320ReleaseHold.bridge.physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.massWitness.positiveMass = true := by
  rfl

theorem physical_witness_3320_release_hold_witness_orthogonal :
    physicalWitness3320ReleaseHold.bridge.physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.sectorSeparation.witnessSector =
      Spectral.SpectralSector.orthogonal := by
  rfl

theorem physical_witness_3320_release_hold_witness_not_vacuum :
    physicalWitness3320ReleaseHold.bridge.physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.sectorSeparation.witnessSector ≠
      Spectral.SpectralSector.vacuum := by
  decide

theorem physical_witness_3320_release_is_held :
    physicalWitness3320ReleaseHold.finalReleaseHeld := by
  trivial

theorem physical_witness_3320_release_public_boundary_locked :
    physicalWitness3320ReleaseHold.publicBoundaryLocked := by
  exact spectral3320_pre_release_checkpoint_boundary_locked

end MGAP4D
