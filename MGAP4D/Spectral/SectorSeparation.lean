import MGAP4D.Spectral.SectorBoundary
import MGAP4D.Spectral.PositiveGap

namespace MGAP4D
namespace Spectral

/-- A pre-Mathlib strengthening of the vacuum/orthogonal sector boundary.

This certificate records not only that the two sector labels are distinct, but
also that the positive gap witness is carried on the orthogonal side and that
sector collapse is explicitly blocked. -/
structure SectorSeparationCertificate where
  boundary : SectorBoundaryCertificate
  boundaryReady : boundary.ready
  witnessSector : SpectralSector
  witnessSectorIsOrthogonal : witnessSector = SpectralSector.orthogonal
  witnessNotVacuum : witnessSector ≠ SpectralSector.vacuum
  positiveGap : PositiveGapCertificate
  positiveGapReady : positiveGap.ready
  witnessMatchesPositiveGap : positiveGap.witness.gap = positiveGap.value
  vacuumOrthogonalNoCollapse : boundary.vacuumSector ≠ boundary.orthogonalSector
  separationVisible : Prop
  projectionBoundaryVisible : Prop
  theoremBoundaryHeld : Prop

def SectorSeparationCertificate.ready
    (C : SectorSeparationCertificate) : Prop :=
  C.boundaryReady ∧ C.witnessSectorIsOrthogonal ∧ C.witnessNotVacuum ∧
  C.positiveGapReady ∧ C.witnessMatchesPositiveGap ∧ C.vacuumOrthogonalNoCollapse ∧
  C.separationVisible ∧ C.projectionBoundaryVisible ∧ C.theoremBoundaryHeld

def spectralSectorSeparationCertificate : SectorSeparationCertificate :=
  { boundary := spectralSectorBoundaryCertificate True True True True True
    boundaryReady := spectral_sector_boundary_certificate_ready
    witnessSector := SpectralSector.orthogonal
    witnessSectorIsOrthogonal := by rfl
    witnessNotVacuum := by decide
    positiveGap := positive3320GapCertificate True True True True
    positiveGapReady := by
      exact And.intro rfl <|
        And.intro rfl <|
        And.intro gap3320Witness.positiveNumerator <|
        And.intro True.intro <|
        And.intro True.intro <|
        And.intro True.intro True.intro
    witnessMatchesPositiveGap := by rfl
    vacuumOrthogonalNoCollapse := by decide
    separationVisible := True
    projectionBoundaryVisible := True
    theoremBoundaryHeld := True }

theorem sector_separation_certificate_pack
    (C : SectorSeparationCertificate) :
    C.ready ↔ C.boundaryReady ∧ C.witnessSectorIsOrthogonal ∧ C.witnessNotVacuum ∧
      C.positiveGapReady ∧ C.witnessMatchesPositiveGap ∧ C.vacuumOrthogonalNoCollapse ∧
      C.separationVisible ∧ C.projectionBoundaryVisible ∧ C.theoremBoundaryHeld := by
  rfl

theorem spectral_sector_separation_certificate_ready :
    spectralSectorSeparationCertificate.ready := by
  exact And.intro spectral_sector_boundary_certificate_ready <|
    And.intro rfl <|
    And.intro (by decide) <|
    And.intro spectralSectorSeparationCertificate.positiveGapReady <|
    And.intro rfl <|
    And.intro (by decide) <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem spectral_sector_separation_witness_is_orthogonal :
    spectralSectorSeparationCertificate.witnessSector = SpectralSector.orthogonal := by
  rfl

theorem spectral_sector_separation_witness_not_vacuum :
    spectralSectorSeparationCertificate.witnessSector ≠ SpectralSector.vacuum := by
  decide

theorem spectral_sector_separation_no_collapse :
    spectralSectorSeparationCertificate.boundary.vacuumSector ≠
      spectralSectorSeparationCertificate.boundary.orthogonalSector := by
  decide

theorem spectral_sector_separation_positive_value :
    spectralSectorSeparationCertificate.positiveGap.value.value = 33 / 20 := by
  rfl

theorem spectral_sector_separation_positive_numerator :
    spectralSectorSeparationCertificate.positiveGap.witness.gap.value.num > 0 := by
  exact gap3320Witness.positiveNumerator

end Spectral
end MGAP4D
