import MGAP4D.PhysicalWitnessReleaseHold

namespace MGAP4D

/-- A pre-Mathlib public-audit checkpoint for the physical witness spine.

This checkpoint packages the physical witness release hold into an auditable
surface: the normalized physical value, the observable spectral weight, the
orthogonal-sector witness, and the public theorem boundary are all visible, but
final release remains held. -/
structure PhysicalWitnessAuditCheckpoint where
  releaseHold : PhysicalWitnessReleaseHold
  releaseHoldReady : releaseHold.ready
  auditCheckpointVisible : Prop
  physicalValueVisible : releaseHold.bridge.physicalWitness.hamiltonianBridge.hamiltonianSpectralBridge.normalization.normalizedGap.value = 33 / 20
  observableWeightVisible : releaseHold.bridge.physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.value = 33 / 20
  observableApgVisible : releaseHold.bridge.physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.observable = Plaquette.A_pg
  positiveObservableMassVisible : releaseHold.bridge.physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.massWitness.positiveMass = true
  orthogonalWitnessVisible : releaseHold.bridge.physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.sectorSeparation.witnessSector = Spectral.SpectralSector.orthogonal
  nonVacuumWitnessVisible : releaseHold.bridge.physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.sectorSeparation.witnessSector ≠ Spectral.SpectralSector.vacuum
  finalReleaseHeld : releaseHold.finalReleaseHeld
  publicBoundaryLocked : releaseHold.publicBoundaryLocked
  theoremCompletionsNotClaimed : releaseHold.theoremCompletionsNotClaimed
  theoremBoundaryHeld : releaseHold.theoremBoundaryHeld

def PhysicalWitnessAuditCheckpoint.ready
    (C : PhysicalWitnessAuditCheckpoint) : Prop :=
  C.releaseHoldReady ∧ C.auditCheckpointVisible ∧ C.physicalValueVisible ∧
  C.observableWeightVisible ∧ C.observableApgVisible ∧ C.positiveObservableMassVisible ∧
  C.orthogonalWitnessVisible ∧ C.nonVacuumWitnessVisible ∧ C.finalReleaseHeld ∧
  C.publicBoundaryLocked ∧ C.theoremCompletionsNotClaimed ∧ C.theoremBoundaryHeld

def physicalWitness3320AuditCheckpoint : PhysicalWitnessAuditCheckpoint :=
  { releaseHold := physicalWitness3320ReleaseHold
    releaseHoldReady := physical_witness_3320_release_hold_ready
    auditCheckpointVisible := True
    physicalValueVisible := by rfl
    observableWeightVisible := by rfl
    observableApgVisible := by rfl
    positiveObservableMassVisible := by rfl
    orthogonalWitnessVisible := by rfl
    nonVacuumWitnessVisible := by decide
    finalReleaseHeld := physical_witness_3320_release_is_held
    publicBoundaryLocked := physical_witness_3320_release_public_boundary_locked
    theoremCompletionsNotClaimed := by trivial
    theoremBoundaryHeld := by trivial }

theorem physical_witness_audit_checkpoint_pack
    (C : PhysicalWitnessAuditCheckpoint) :
    C.ready ↔ C.releaseHoldReady ∧ C.auditCheckpointVisible ∧ C.physicalValueVisible ∧
      C.observableWeightVisible ∧ C.observableApgVisible ∧ C.positiveObservableMassVisible ∧
      C.orthogonalWitnessVisible ∧ C.nonVacuumWitnessVisible ∧ C.finalReleaseHeld ∧
      C.publicBoundaryLocked ∧ C.theoremCompletionsNotClaimed ∧ C.theoremBoundaryHeld := by
  rfl

theorem physical_witness_3320_audit_checkpoint_ready :
    physicalWitness3320AuditCheckpoint.ready := by
  exact And.intro physical_witness_3320_release_hold_ready <|
    And.intro True.intro <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro (by decide) <|
    And.intro physical_witness_3320_release_is_held <|
    And.intro physical_witness_3320_release_public_boundary_locked <|
    And.intro True.intro True.intro

theorem physical_witness_3320_audit_checkpoint_physical_value :
    physicalWitness3320AuditCheckpoint.releaseHold.bridge.physicalWitness.hamiltonianBridge.hamiltonianSpectralBridge.normalization.normalizedGap.value = 33 / 20 := by
  rfl

theorem physical_witness_3320_audit_checkpoint_observable_value :
    physicalWitness3320AuditCheckpoint.releaseHold.bridge.physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.value = 33 / 20 := by
  rfl

theorem physical_witness_3320_audit_checkpoint_observable_Apg :
    physicalWitness3320AuditCheckpoint.releaseHold.bridge.physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.observable = Plaquette.A_pg := by
  rfl

theorem physical_witness_3320_audit_checkpoint_positive_mass :
    physicalWitness3320AuditCheckpoint.releaseHold.bridge.physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.massWitness.positiveMass = true := by
  rfl

theorem physical_witness_3320_audit_checkpoint_orthogonal :
    physicalWitness3320AuditCheckpoint.releaseHold.bridge.physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.sectorSeparation.witnessSector = Spectral.SpectralSector.orthogonal := by
  rfl

theorem physical_witness_3320_audit_checkpoint_not_vacuum :
    physicalWitness3320AuditCheckpoint.releaseHold.bridge.physicalWitness.observableClosure.bridge.finalBridge.spectralWeight.sectorSeparation.witnessSector ≠ Spectral.SpectralSector.vacuum := by
  decide

theorem physical_witness_3320_audit_checkpoint_release_held :
    physicalWitness3320AuditCheckpoint.finalReleaseHeld := by
  exact physical_witness_3320_release_is_held

theorem physical_witness_3320_audit_checkpoint_public_boundary_locked :
    physicalWitness3320AuditCheckpoint.publicBoundaryLocked := by
  exact physical_witness_3320_release_public_boundary_locked

end MGAP4D
