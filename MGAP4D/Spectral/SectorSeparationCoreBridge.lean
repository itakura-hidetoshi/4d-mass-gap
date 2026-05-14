import MGAP4D.Spectral.CoreCertificate
import MGAP4D.Spectral.SectorSeparation

namespace MGAP4D
namespace Spectral

/-- A pre-Mathlib bridge from sector separation into the spectral core certificate.

This makes the stronger vacuum/orthogonal separation surface visible from the
core certificate without changing final theorem-release status. -/
structure SectorSeparationCoreBridge where
  core : SpectralCoreCertificate
  coreReady : core.ready
  separation : SectorSeparationCertificate
  separationReady : separation.ready
  separationBoundaryMatchesCore : separation.boundary = core.lowerBound.sectorBoundary
  separationWitnessMatchesCore : separation.positiveGap.witness = core.formalization.witness
  witnessSectorIsOrthogonal : separation.witnessSector = SpectralSector.orthogonal
  witnessNotVacuum : separation.witnessSector ≠ SpectralSector.vacuum
  vacuumOrthogonalNoCollapse : separation.boundary.vacuumSector ≠ separation.boundary.orthogonalSector
  bridgeVisible : Prop
  theoremBoundaryHeld : Prop

def SectorSeparationCoreBridge.ready
    (B : SectorSeparationCoreBridge) : Prop :=
  B.coreReady ∧ B.separationReady ∧ B.separationBoundaryMatchesCore ∧
  B.separationWitnessMatchesCore ∧ B.witnessSectorIsOrthogonal ∧ B.witnessNotVacuum ∧
  B.vacuumOrthogonalNoCollapse ∧ B.bridgeVisible ∧ B.theoremBoundaryHeld

def spectral3320SectorSeparationCoreBridge : SectorSeparationCoreBridge :=
  { core := spectral3320CoreCertificate
    coreReady := spectral_3320_core_certificate_ready
    separation := spectralSectorSeparationCertificate
    separationReady := spectral_sector_separation_certificate_ready
    separationBoundaryMatchesCore := by rfl
    separationWitnessMatchesCore := by rfl
    witnessSectorIsOrthogonal := by rfl
    witnessNotVacuum := by decide
    vacuumOrthogonalNoCollapse := by decide
    bridgeVisible := True
    theoremBoundaryHeld := True }

theorem sector_separation_core_bridge_pack
    (B : SectorSeparationCoreBridge) :
    B.ready ↔ B.coreReady ∧ B.separationReady ∧ B.separationBoundaryMatchesCore ∧
      B.separationWitnessMatchesCore ∧ B.witnessSectorIsOrthogonal ∧ B.witnessNotVacuum ∧
      B.vacuumOrthogonalNoCollapse ∧ B.bridgeVisible ∧ B.theoremBoundaryHeld := by
  rfl

theorem spectral3320_sector_separation_core_bridge_ready :
    spectral3320SectorSeparationCoreBridge.ready := by
  exact And.intro spectral_3320_core_certificate_ready <|
    And.intro spectral_sector_separation_certificate_ready <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro (by decide) <|
    And.intro (by decide) <|
    And.intro True.intro True.intro

theorem spectral3320_sector_separation_core_bridge_value :
    spectral3320SectorSeparationCoreBridge.core.formalization.normalizedGapValue.value = 33 / 20 := by
  rfl

theorem spectral3320_sector_separation_core_bridge_positive_numerator :
    spectral3320SectorSeparationCoreBridge.separation.positiveGap.witness.gap.value.num > 0 := by
  exact gap3320Witness.positiveNumerator

theorem spectral3320_sector_separation_core_bridge_witness_orthogonal :
    spectral3320SectorSeparationCoreBridge.separation.witnessSector = SpectralSector.orthogonal := by
  rfl

theorem spectral3320_sector_separation_core_bridge_witness_not_vacuum :
    spectral3320SectorSeparationCoreBridge.separation.witnessSector ≠ SpectralSector.vacuum := by
  decide

theorem spectral3320_sector_separation_core_bridge_no_collapse :
    spectral3320SectorSeparationCoreBridge.separation.boundary.vacuumSector ≠
      spectral3320SectorSeparationCoreBridge.separation.boundary.orthogonalSector := by
  decide

end Spectral
end MGAP4D
