import MGAP4D.Plaquette.ObservableSpectralWeight
import MGAP4D.Hamiltonian.EigenvectorConstruction

namespace MGAP4D
namespace Plaquette

/-- Named pre-Mathlib targets for the observable spectral-projection surface.

This is the sixth residual-resolution target: expose the proof-body pieces
needed to replace the structural positive spectral-weight witness by an analytic
spectral-projection theorem at the normalized `33/20` value. -/
inductive ObservableSpectralProjectionTarget where
  | observableCarrier
  | centeredCompactSupport
  | spectralMassAt3320
  | positiveMassToProjectionNonzero
  | orthogonalSectorDetection
  | witnessCompatibility
  | sharpGapCompatibility
  deriving Repr, DecidableEq

/-- A pre-Mathlib observable spectral-projection surface.

The surface records the theorem-body obligations for showing that the compactly
supported centered plaquette observable `A_pg` detects the `33/20` spectral
surface.  It is structural only; the projection-valued-measure theorem is a
later Mathlib-backed replacement. -/
structure ObservableSpectralProjectionSurface where
  spectralWeight : ObservableSpectralWeightCertificate
  spectralWeightReady : spectralWeight.ready
  psiStarSurface : Hamiltonian.EigenvectorConstructionSurface
  psiStarSurfaceReady : psiStarSurface.ready
  observableCarrierSurface : spectralWeight.observable = A_pg
  centeredCompactSupportSurface : spectralWeight.observable.centered = true ∧ spectralWeight.observable.smearing.compactSupport = true
  spectralMassAt3320Surface : spectralWeight.massWitness.value = 33 / 20
  positiveMassSurface : spectralWeight.massWitness.positiveMass = true
  positiveMassToProjectionNonzeroSurface : Prop
  orthogonalSectorDetectionSurface : spectralWeight.sectorSeparation.witnessSector = Spectral.SpectralSector.orthogonal
  witnessCompatibilitySurface : psiStarSurface.physicalEigenWitness.eigenWitness.eigenvalue = spectralWeight.massWitness.value
  sharpGapCompatibilitySurface : Prop
  exactGapValue3320 : psiStarSurface.lowerBoundProofBody.gapInfimum.exactGap.exactGapValue = 33 / 20
  finalReleaseHeld : psiStarSurface.finalReleaseHeld
  publicBoundaryLocked : psiStarSurface.publicBoundaryLocked
  noAutoRelease : psiStarSurface.noAutoRelease
  theoremBoundaryHeld : psiStarSurface.theoremBoundaryHeld

def ObservableSpectralProjectionSurface.ready
    (S : ObservableSpectralProjectionSurface) : Prop :=
  S.spectralWeightReady ∧ S.psiStarSurfaceReady ∧ S.observableCarrierSurface ∧
  S.centeredCompactSupportSurface ∧ S.spectralMassAt3320Surface ∧
  S.positiveMassSurface ∧ S.positiveMassToProjectionNonzeroSurface ∧
  S.orthogonalSectorDetectionSurface ∧ S.witnessCompatibilitySurface ∧
  S.sharpGapCompatibilitySurface ∧ S.exactGapValue3320 ∧ S.finalReleaseHeld ∧
  S.publicBoundaryLocked ∧ S.noAutoRelease ∧ S.theoremBoundaryHeld

def observableSpectralProjection3320Surface : ObservableSpectralProjectionSurface :=
  { spectralWeight := observableSpectralWeight3320Certificate
    spectralWeightReady := observable_spectral_weight_3320_certificate_ready
    psiStarSurface := Hamiltonian.eigenvector3320ConstructionSurface
    psiStarSurfaceReady := Hamiltonian.eigenvector_3320_construction_surface_ready
    observableCarrierSurface := by rfl
    centeredCompactSupportSurface := And.intro observable_spectral_weight_3320_centered observable_spectral_weight_3320_compact_support
    spectralMassAt3320Surface := observable_spectral_weight_3320_mass_value
    positiveMassSurface := observable_spectral_weight_3320_positive_mass
    positiveMassToProjectionNonzeroSurface := True
    orthogonalSectorDetectionSurface := observable_spectral_weight_3320_witness_orthogonal
    witnessCompatibilitySurface := by rfl
    sharpGapCompatibilitySurface := True
    exactGapValue3320 := Hamiltonian.eigenvector_3320_construction_exact_value
    finalReleaseHeld := Hamiltonian.eigenvector_3320_construction_release_held
    publicBoundaryLocked := Hamiltonian.eigenvector_3320_construction_public_boundary_locked
    noAutoRelease := Hamiltonian.eigenvector_3320_construction_no_auto_release
    theoremBoundaryHeld := by trivial }

theorem observable_spectral_projection_surface_pack
    (S : ObservableSpectralProjectionSurface) :
    S.ready ↔ S.spectralWeightReady ∧ S.psiStarSurfaceReady ∧
      S.observableCarrierSurface ∧ S.centeredCompactSupportSurface ∧
      S.spectralMassAt3320Surface ∧ S.positiveMassSurface ∧
      S.positiveMassToProjectionNonzeroSurface ∧ S.orthogonalSectorDetectionSurface ∧
      S.witnessCompatibilitySurface ∧ S.sharpGapCompatibilitySurface ∧
      S.exactGapValue3320 ∧ S.finalReleaseHeld ∧ S.publicBoundaryLocked ∧
      S.noAutoRelease ∧ S.theoremBoundaryHeld := by
  rfl

theorem observable_spectral_projection_3320_surface_ready :
    observableSpectralProjection3320Surface.ready := by
  exact And.intro observable_spectral_weight_3320_certificate_ready <|
    And.intro Hamiltonian.eigenvector_3320_construction_surface_ready <|
    And.intro rfl <|
    And.intro (And.intro observable_spectral_weight_3320_centered observable_spectral_weight_3320_compact_support) <|
    And.intro observable_spectral_weight_3320_mass_value <|
    And.intro observable_spectral_weight_3320_positive_mass <|
    And.intro True.intro <|
    And.intro observable_spectral_weight_3320_witness_orthogonal <|
    And.intro rfl <|
    And.intro True.intro <|
    And.intro Hamiltonian.eigenvector_3320_construction_exact_value <|
    And.intro Hamiltonian.eigenvector_3320_construction_release_held <|
    And.intro Hamiltonian.eigenvector_3320_construction_public_boundary_locked <|
    And.intro Hamiltonian.eigenvector_3320_construction_no_auto_release True.intro

theorem observable_spectral_projection_3320_mass_value :
    observableSpectralProjection3320Surface.spectralWeight.massWitness.value = 33 / 20 := by
  exact observable_spectral_weight_3320_mass_value

theorem observable_spectral_projection_3320_positive_mass :
    observableSpectralProjection3320Surface.spectralWeight.massWitness.positiveMass = true := by
  exact observable_spectral_weight_3320_positive_mass

theorem observable_spectral_projection_3320_observable_is_Apg :
    observableSpectralProjection3320Surface.spectralWeight.observable = A_pg := by
  rfl

theorem observable_spectral_projection_3320_centered_compact :
    observableSpectralProjection3320Surface.centeredCompactSupportSurface := by
  exact And.intro observable_spectral_weight_3320_centered observable_spectral_weight_3320_compact_support

theorem observable_spectral_projection_3320_detection_orthogonal :
    observableSpectralProjection3320Surface.orthogonalSectorDetectionSurface := by
  exact observable_spectral_weight_3320_witness_orthogonal

theorem observable_spectral_projection_3320_witness_compatibility :
    observableSpectralProjection3320Surface.witnessCompatibilitySurface := by
  rfl

theorem observable_spectral_projection_3320_projection_nonzero_surface :
    observableSpectralProjection3320Surface.positiveMassToProjectionNonzeroSurface := by
  trivial

theorem observable_spectral_projection_3320_exact_value :
    observableSpectralProjection3320Surface.psiStarSurface.lowerBoundProofBody.gapInfimum.exactGap.exactGapValue = 33 / 20 := by
  exact Hamiltonian.eigenvector_3320_construction_exact_value

theorem observable_spectral_projection_3320_release_held :
    observableSpectralProjection3320Surface.finalReleaseHeld := by
  exact Hamiltonian.eigenvector_3320_construction_release_held

theorem observable_spectral_projection_3320_public_boundary_locked :
    observableSpectralProjection3320Surface.publicBoundaryLocked := by
  exact Hamiltonian.eigenvector_3320_construction_public_boundary_locked

theorem observable_spectral_projection_3320_no_auto_release :
    observableSpectralProjection3320Surface.noAutoRelease := by
  exact Hamiltonian.eigenvector_3320_construction_no_auto_release

end Plaquette
end MGAP4D
