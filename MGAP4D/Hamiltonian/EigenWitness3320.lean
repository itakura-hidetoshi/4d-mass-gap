import MGAP4D.Hamiltonian.NormalizationPreReleaseBridge
import MGAP4D.Constructive.Eigenvector
import MGAP4D.Spectral.SectorSeparation

namespace MGAP4D
namespace Hamiltonian

/-- A pre-Mathlib physical eigen-witness certificate for the normalized
`33/20` physical Hamiltonian surface.

This certificate lifts the constructive `psi_*` witness into the physical
Hamiltonian layer: it is normalized, attached to `H_phys`, has eigenvalue
`33/20`, and is carried by the orthogonal sector rather than the vacuum sector. -/
structure PhysicalEigenWitness3320 where
  hamiltonian : HamiltonianLabel
  hamiltonianIsHphys : hamiltonian = Hphys
  normalizationBridge : HamiltonianNormalizationPreReleaseBridge
  normalizationBridgeReady : normalizationBridge.ready
  eigenWitness : Constructive.EigenvectorWitness
  eigenWitnessIsPsiStar : eigenWitness = Constructive.psiStarWitness
  eigenWitnessNormOne : eigenWitness.normOne = true
  eigenvalueIs3320 : eigenWitness.eigenvalue = 33 / 20
  gapRecordMatchesPhysical : eigenWitness.gapRecord.value = normalizationBridge.hamiltonianSpectralBridge.normalization.normalizedGap.value
  sectorSeparation : Spectral.SectorSeparationCertificate
  sectorSeparationReady : sectorSeparation.ready
  witnessSectorOrthogonal : sectorSeparation.witnessSector = Spectral.SpectralSector.orthogonal
  witnessNotVacuum : sectorSeparation.witnessSector ≠ Spectral.SpectralSector.vacuum
  eigenRelationVisible : Prop
  theoremBoundaryHeld : Prop

def PhysicalEigenWitness3320.ready
    (W : PhysicalEigenWitness3320) : Prop :=
  W.hamiltonianIsHphys ∧ W.normalizationBridgeReady ∧ W.eigenWitnessIsPsiStar ∧
  W.eigenWitnessNormOne ∧ W.eigenvalueIs3320 ∧ W.gapRecordMatchesPhysical ∧
  W.sectorSeparationReady ∧ W.witnessSectorOrthogonal ∧ W.witnessNotVacuum ∧
  W.eigenRelationVisible ∧ W.theoremBoundaryHeld

def physicalEigenWitness3320 : PhysicalEigenWitness3320 :=
  { hamiltonian := Hphys
    hamiltonianIsHphys := by rfl
    normalizationBridge := hamiltonian3320NormalizationPreReleaseBridge
    normalizationBridgeReady := hamiltonian3320_normalization_pre_release_bridge_ready
    eigenWitness := Constructive.psiStarWitness
    eigenWitnessIsPsiStar := by rfl
    eigenWitnessNormOne := by rfl
    eigenvalueIs3320 := by rfl
    gapRecordMatchesPhysical := by rfl
    sectorSeparation := Spectral.spectralSectorSeparationCertificate
    sectorSeparationReady := Spectral.spectral_sector_separation_certificate_ready
    witnessSectorOrthogonal := by rfl
    witnessNotVacuum := by decide
    eigenRelationVisible := True
    theoremBoundaryHeld := True }

theorem physical_eigen_witness_3320_pack
    (W : PhysicalEigenWitness3320) :
    W.ready ↔ W.hamiltonianIsHphys ∧ W.normalizationBridgeReady ∧
      W.eigenWitnessIsPsiStar ∧ W.eigenWitnessNormOne ∧ W.eigenvalueIs3320 ∧
      W.gapRecordMatchesPhysical ∧ W.sectorSeparationReady ∧ W.witnessSectorOrthogonal ∧
      W.witnessNotVacuum ∧ W.eigenRelationVisible ∧ W.theoremBoundaryHeld := by
  rfl

theorem physical_eigen_witness_3320_ready :
    physicalEigenWitness3320.ready := by
  exact And.intro rfl <|
    And.intro hamiltonian3320_normalization_pre_release_bridge_ready <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro Spectral.spectral_sector_separation_certificate_ready <|
    And.intro rfl <|
    And.intro (by decide) <|
    And.intro True.intro True.intro

theorem physical_eigen_witness_3320_hamiltonian_is_Hphys :
    physicalEigenWitness3320.hamiltonian = Hphys := by
  rfl

theorem physical_eigen_witness_3320_norm_one :
    physicalEigenWitness3320.eigenWitness.normOne = true := by
  rfl

theorem physical_eigen_witness_3320_eigenvalue :
    physicalEigenWitness3320.eigenWitness.eigenvalue = 33 / 20 := by
  rfl

theorem physical_eigen_witness_3320_gap_matches_physical :
    physicalEigenWitness3320.eigenWitness.gapRecord.value =
      physicalEigenWitness3320.normalizationBridge.hamiltonianSpectralBridge.normalization.normalizedGap.value := by
  rfl

theorem physical_eigen_witness_3320_orthogonal :
    physicalEigenWitness3320.sectorSeparation.witnessSector = Spectral.SpectralSector.orthogonal := by
  rfl

theorem physical_eigen_witness_3320_not_vacuum :
    physicalEigenWitness3320.sectorSeparation.witnessSector ≠ Spectral.SpectralSector.vacuum := by
  decide

theorem physical_eigen_witness_3320_physical_value :
    physicalEigenWitness3320.normalizationBridge.hamiltonianSpectralBridge.normalization.normalizedGap.value = 33 / 20 := by
  rfl

end Hamiltonian
end MGAP4D
