import MGAP4D.Hamiltonian.NormalizationPreReleaseBridge
import MGAP4D.Constructive.ObservableSpectralWeightClosure

namespace MGAP4D

/-- A pre-Mathlib aggregate closure for the physical witness spine.

This closure binds together the normalized physical Hamiltonian surface, the
observable spectral-weight closure, the orthogonal-sector witness, and the
review-gated public-boundary lock. It is an aggregate tracking surface only; it
does not open final theorem release. -/
structure PhysicalWitnessClosure where
  hamiltonianBridge : Hamiltonian.HamiltonianNormalizationPreReleaseBridge
  hamiltonianBridgeReady : hamiltonianBridge.ready
  observableClosure : Constructive.ObservableSpectralWeightClosure
  observableClosureReady : observableClosure.ready
  normalizedGapMatchesObservableWeight :
    hamiltonianBridge.hamiltonianSpectralBridge.normalization.normalizedGap.value =
      observableClosure.bridge.finalBridge.spectralWeight.value
  hphysUnitScaleOne : hamiltonianBridge.hamiltonianSpectralBridge.normalization.unit.unitScale = 1
  hphysVacuumReferenceZero : hamiltonianBridge.hamiltonianSpectralBridge.normalization.unit.vacuumEnergyReference = 0
  observableIsApg : observableClosure.bridge.finalBridge.spectralWeight.observable = Plaquette.A_pg
  observablePositiveMass : observableClosure.bridge.finalBridge.spectralWeight.massWitness.positiveMass = true
  witnessSectorOrthogonal :
    observableClosure.bridge.finalBridge.spectralWeight.sectorSeparation.witnessSector = Spectral.SpectralSector.orthogonal
  witnessNotVacuum :
    observableClosure.bridge.finalBridge.spectralWeight.sectorSeparation.witnessSector ≠ Spectral.SpectralSector.vacuum
  publicBoundaryLocked : observableClosure.bridge.preReleaseCheckpoint.publicBoundaryLocked
  theoremBoundaryHeld : Prop

/-- Readiness is a proposition-level checklist.  Proof-carrying fields are
re-expanded to their underlying propositions, rather than being reused as proof
terms inside the `∧` chain. -/
def PhysicalWitnessClosure.ready
    (C : PhysicalWitnessClosure) : Prop :=
  C.hamiltonianBridge.ready ∧ C.observableClosure.ready ∧
  C.hamiltonianBridge.hamiltonianSpectralBridge.normalization.normalizedGap.value =
    C.observableClosure.bridge.finalBridge.spectralWeight.value ∧
  C.hamiltonianBridge.hamiltonianSpectralBridge.normalization.unit.unitScale = 1 ∧
  C.hamiltonianBridge.hamiltonianSpectralBridge.normalization.unit.vacuumEnergyReference = 0 ∧
  C.observableClosure.bridge.finalBridge.spectralWeight.observable = Plaquette.A_pg ∧
  C.observableClosure.bridge.finalBridge.spectralWeight.massWitness.positiveMass = true ∧
  C.observableClosure.bridge.finalBridge.spectralWeight.sectorSeparation.witnessSector = Spectral.SpectralSector.orthogonal ∧
  C.observableClosure.bridge.finalBridge.spectralWeight.sectorSeparation.witnessSector ≠ Spectral.SpectralSector.vacuum ∧
  C.observableClosure.bridge.preReleaseCheckpoint.publicBoundaryLocked ∧
  C.theoremBoundaryHeld

def physicalWitness3320Closure : PhysicalWitnessClosure :=
  { hamiltonianBridge := Hamiltonian.hamiltonian3320NormalizationPreReleaseBridge
    hamiltonianBridgeReady := Hamiltonian.hamiltonian3320_normalization_pre_release_bridge_ready
    observableClosure := Constructive.observableSpectralWeight3320Closure
    observableClosureReady := Constructive.observable_spectral_weight_3320_closure_ready
    normalizedGapMatchesObservableWeight := by rfl
    hphysUnitScaleOne := by rfl
    hphysVacuumReferenceZero := by rfl
    observableIsApg := by rfl
    observablePositiveMass := by rfl
    witnessSectorOrthogonal := by rfl
    witnessNotVacuum := by decide
    publicBoundaryLocked := spectral3320_pre_release_checkpoint_boundary_locked
    theoremBoundaryHeld := True }

theorem physical_witness_closure_pack
    (C : PhysicalWitnessClosure) :
    C.ready ↔ C.hamiltonianBridge.ready ∧ C.observableClosure.ready ∧
      C.hamiltonianBridge.hamiltonianSpectralBridge.normalization.normalizedGap.value =
        C.observableClosure.bridge.finalBridge.spectralWeight.value ∧
      C.hamiltonianBridge.hamiltonianSpectralBridge.normalization.unit.unitScale = 1 ∧
      C.hamiltonianBridge.hamiltonianSpectralBridge.normalization.unit.vacuumEnergyReference = 0 ∧
      C.observableClosure.bridge.finalBridge.spectralWeight.observable = Plaquette.A_pg ∧
      C.observableClosure.bridge.finalBridge.spectralWeight.massWitness.positiveMass = true ∧
      C.observableClosure.bridge.finalBridge.spectralWeight.sectorSeparation.witnessSector = Spectral.SpectralSector.orthogonal ∧
      C.observableClosure.bridge.finalBridge.spectralWeight.sectorSeparation.witnessSector ≠ Spectral.SpectralSector.vacuum ∧
      C.observableClosure.bridge.preReleaseCheckpoint.publicBoundaryLocked ∧
      C.theoremBoundaryHeld := by
  rfl

theorem physical_witness_3320_closure_ready :
    physicalWitness3320Closure.ready := by
  exact And.intro Hamiltonian.hamiltonian3320_normalization_pre_release_bridge_ready <|
    And.intro Constructive.observable_spectral_weight_3320_closure_ready <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro (by decide) <|
    And.intro spectral3320_pre_release_checkpoint_boundary_locked True.intro

theorem physical_witness_3320_normalized_gap_value :
    physicalWitness3320Closure.hamiltonianBridge.hamiltonianSpectralBridge.normalization.normalizedGap.value = 33 / 20 := by
  rfl

theorem physical_witness_3320_observable_weight_value :
    physicalWitness3320Closure.observableClosure.bridge.finalBridge.spectralWeight.value = 33 / 20 := by
  rfl

theorem physical_witness_3320_unit_scale_one :
    physicalWitness3320Closure.hamiltonianBridge.hamiltonianSpectralBridge.normalization.unit.unitScale = 1 := by
  rfl

theorem physical_witness_3320_vacuum_reference_zero :
    physicalWitness3320Closure.hamiltonianBridge.hamiltonianSpectralBridge.normalization.unit.vacuumEnergyReference = 0 := by
  rfl

theorem physical_witness_3320_observable_is_Apg :
    physicalWitness3320Closure.observableClosure.bridge.finalBridge.spectralWeight.observable = Plaquette.A_pg := by
  rfl

theorem physical_witness_3320_positive_mass :
    physicalWitness3320Closure.observableClosure.bridge.finalBridge.spectralWeight.massWitness.positiveMass = true := by
  rfl

theorem physical_witness_3320_witness_orthogonal :
    physicalWitness3320Closure.observableClosure.bridge.finalBridge.spectralWeight.sectorSeparation.witnessSector =
      Spectral.SpectralSector.orthogonal := by
  rfl

theorem physical_witness_3320_witness_not_vacuum :
    physicalWitness3320Closure.observableClosure.bridge.finalBridge.spectralWeight.sectorSeparation.witnessSector ≠
      Spectral.SpectralSector.vacuum := by
  decide

theorem physical_witness_3320_public_boundary_locked :
    physicalWitness3320Closure.publicBoundaryLocked := by
  exact spectral3320_pre_release_checkpoint_boundary_locked

end MGAP4D
