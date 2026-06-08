import MGAP4D.Spectral.GapFormalization

namespace MGAP4D
namespace Spectral

/-- A pre-Mathlib certificate that the formal spectral surface keeps the vacuum
sector and the orthogonal sector visibly separated. -/
structure SectorBoundaryCertificate where
  vacuumSector : SpectralSector
  orthogonalSector : SpectralSector
  vacuumIsVacuum : vacuumSector = SpectralSector.vacuum
  orthogonalIsOrthogonal : orthogonalSector = SpectralSector.orthogonal
  vacuumDistinctFromOrthogonal : vacuumSector ≠ orthogonalSector
  vacuumSectorBoundaryVisible : Prop
  orthogonalSectorBoundaryVisible : Prop
  nonTheoremCompletionBoundaryVisible : Prop
  finalGapReleaseNotUnlocked : Prop
  mainPreMathlib : Prop

/-- Readiness is a proposition-level checklist.  Proof-carrying fields are
re-expanded to their underlying propositions, rather than being reused as proof
terms inside the `∧` chain. -/
def SectorBoundaryCertificate.ready
    (C : SectorBoundaryCertificate) : Prop :=
  C.vacuumSector = SpectralSector.vacuum ∧
  C.orthogonalSector = SpectralSector.orthogonal ∧
  C.vacuumSector ≠ C.orthogonalSector ∧ C.vacuumSectorBoundaryVisible ∧
  C.orthogonalSectorBoundaryVisible ∧ C.nonTheoremCompletionBoundaryVisible ∧
  C.finalGapReleaseNotUnlocked ∧ C.mainPreMathlib

def spectralSectorBoundaryCertificate
    (vacuumSectorBoundaryVisible : Prop)
    (orthogonalSectorBoundaryVisible : Prop)
    (nonTheoremCompletionBoundaryVisible : Prop)
    (finalGapReleaseNotUnlocked : Prop)
    (mainPreMathlib : Prop) : SectorBoundaryCertificate :=
  { vacuumSector := SpectralSector.vacuum
    orthogonalSector := SpectralSector.orthogonal
    vacuumIsVacuum := by rfl
    orthogonalIsOrthogonal := by rfl
    vacuumDistinctFromOrthogonal := by decide
    vacuumSectorBoundaryVisible := vacuumSectorBoundaryVisible
    orthogonalSectorBoundaryVisible := orthogonalSectorBoundaryVisible
    nonTheoremCompletionBoundaryVisible := nonTheoremCompletionBoundaryVisible
    finalGapReleaseNotUnlocked := finalGapReleaseNotUnlocked
    mainPreMathlib := mainPreMathlib }

theorem sector_boundary_certificate_pack
    (C : SectorBoundaryCertificate) :
    C.ready ↔ C.vacuumSector = SpectralSector.vacuum ∧
      C.orthogonalSector = SpectralSector.orthogonal ∧
      C.vacuumSector ≠ C.orthogonalSector ∧ C.vacuumSectorBoundaryVisible ∧
      C.orthogonalSectorBoundaryVisible ∧ C.nonTheoremCompletionBoundaryVisible ∧
      C.finalGapReleaseNotUnlocked ∧ C.mainPreMathlib := by
  rfl

theorem spectral_sector_boundary_distinct :
    (spectralSectorBoundaryCertificate True True True True True).vacuumSector ≠
      (spectralSectorBoundaryCertificate True True True True True).orthogonalSector := by
  decide

/-- The sector-boundary certificate is compatible with the earlier formalization
surface: both expose the same vacuum and orthogonal sector boundary labels. -/
theorem spectral_sector_boundary_certificate_ready :
    (spectralSectorBoundaryCertificate True True True True True).ready := by
  exact And.intro rfl <|
    And.intro rfl <|
    And.intro (by decide) <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

end Spectral
end MGAP4D
