import MGAP4D.Hamiltonian.Normalization
import MGAP4D.Spectral.CoreCertificate

namespace MGAP4D
namespace Hamiltonian

/-- A pre-Mathlib bridge connecting the physical Hamiltonian normalization
surface to the spectral core certificate.

This bridge records that the normalized `H_phys` gap record and the spectral
core certificate share the same `33/20` value and the same positive witness. -/
structure HamiltonianSpectralNormalizationBridge where
  normalization : PhysicalHamiltonianNormalization
  normalizationReady : normalization.ready
  spectralCore : Spectral.SpectralCoreCertificate
  spectralCoreReady : spectralCore.ready
  normalizedGapMatchesSpectralCore : normalization.normalizedGap = spectralCore.formalization.normalizedGapValue
  recordWitnessMatchesSpectralCore : normalization.physicalGapRecord.witness = spectralCore.formalization.witness
  unitScaleIsOne : normalization.unit.unitScale = 1
  vacuumReferenceIsZero : normalization.unit.vacuumEnergyReference = 0
  positiveNumeratorPreserved : normalization.physicalGapRecord.witness.gap.value.num > 0
  bridgeVisible : Prop
  theoremBoundaryHeld : Prop

def HamiltonianSpectralNormalizationBridge.ready
    (B : HamiltonianSpectralNormalizationBridge) : Prop :=
  B.normalizationReady ∧ B.spectralCoreReady ∧ B.normalizedGapMatchesSpectralCore ∧
  B.recordWitnessMatchesSpectralCore ∧ B.unitScaleIsOne ∧ B.vacuumReferenceIsZero ∧
  B.positiveNumeratorPreserved ∧ B.bridgeVisible ∧ B.theoremBoundaryHeld

def hamiltonianSpectral3320NormalizationBridge : HamiltonianSpectralNormalizationBridge :=
  { normalization := physicalHamiltonian3320Normalization
    normalizationReady := physical_hamiltonian_3320_normalization_ready
    spectralCore := Spectral.spectral3320CoreCertificate
    spectralCoreReady := Spectral.spectral_3320_core_certificate_ready
    normalizedGapMatchesSpectralCore := by rfl
    recordWitnessMatchesSpectralCore := by rfl
    unitScaleIsOne := by rfl
    vacuumReferenceIsZero := by rfl
    positiveNumeratorPreserved := Spectral.gap3320Witness.positiveNumerator
    bridgeVisible := True
    theoremBoundaryHeld := True }

theorem hamiltonian_spectral_normalization_bridge_pack
    (B : HamiltonianSpectralNormalizationBridge) :
    B.ready ↔ B.normalizationReady ∧ B.spectralCoreReady ∧
      B.normalizedGapMatchesSpectralCore ∧ B.recordWitnessMatchesSpectralCore ∧
      B.unitScaleIsOne ∧ B.vacuumReferenceIsZero ∧ B.positiveNumeratorPreserved ∧
      B.bridgeVisible ∧ B.theoremBoundaryHeld := by
  rfl

theorem hamiltonian_spectral_3320_normalization_bridge_ready :
    hamiltonianSpectral3320NormalizationBridge.ready := by
  exact And.intro physical_hamiltonian_3320_normalization_ready <|
    And.intro Spectral.spectral_3320_core_certificate_ready <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro Spectral.gap3320Witness.positiveNumerator <|
    And.intro True.intro True.intro

theorem hamiltonian_spectral_3320_bridge_value :
    hamiltonianSpectral3320NormalizationBridge.normalization.normalizedGap.value = 33 / 20 := by
  rfl

theorem hamiltonian_spectral_3320_bridge_core_value :
    hamiltonianSpectral3320NormalizationBridge.spectralCore.formalization.normalizedGapValue.value = 33 / 20 := by
  rfl

theorem hamiltonian_spectral_3320_bridge_preserves_positive_numerator :
    hamiltonianSpectral3320NormalizationBridge.normalization.physicalGapRecord.witness.gap.value.num > 0 := by
  exact Spectral.gap3320Witness.positiveNumerator

theorem hamiltonian_spectral_3320_bridge_unit_scale_one :
    hamiltonianSpectral3320NormalizationBridge.normalization.unit.unitScale = 1 := by
  rfl

theorem hamiltonian_spectral_3320_bridge_vacuum_reference_zero :
    hamiltonianSpectral3320NormalizationBridge.normalization.unit.vacuumEnergyReference = 0 := by
  rfl

end Hamiltonian
end MGAP4D
