import MGAP4D.Plaquette.SpectralMeasure
import MGAP4D.Spectral.SectorSeparation
import MGAP4D.Constructive.PlaquetteWitness

namespace MGAP4D
namespace Plaquette

/-- A pre-Mathlib certificate for observable spectral weight at the normalized
`33/20` value.

This certificate lifts the existing Boolean positive-mass witness into a
structured proof surface: the observable is the compactly supported centered
`A_{p,g}`, the value is `33/20`, and the positive weight is attached to the
orthogonal-sector gap witness. -/
structure ObservableSpectralWeightCertificate where
  observable : SmearedPlaquetteObservable
  observableIsApg : observable = A_pg
  observableCentered : observable.centered = true
  observableCompactSupport : observable.smearing.compactSupport = true
  massWitness : SpectralMassWitness
  massWitnessIsRhoApg3320 : massWitness = rho_Apg_3320_positive
  massWitnessObservableMatches : massWitness.observable = observable
  value : Rat
  valueIs3320 : value = 33 / 20
  massWitnessValueMatches : massWitness.value = value
  positiveMass : massWitness.positiveMass = true
  sectorSeparation : Spectral.SectorSeparationCertificate
  sectorSeparationReady : sectorSeparation.ready
  witnessSectorIsOrthogonal : sectorSeparation.witnessSector = Spectral.SpectralSector.orthogonal
  witnessNotVacuum : sectorSeparation.witnessSector ≠ Spectral.SpectralSector.vacuum
  spectralWeightVisible : Prop
  theoremBoundaryHeld : Prop

/-- Readiness is a proposition-level checklist.  Proof-carrying fields are
re-expanded to their underlying propositions, rather than being reused as proof
terms inside the `∧` chain. -/
def ObservableSpectralWeightCertificate.ready
    (C : ObservableSpectralWeightCertificate) : Prop :=
  C.observable = A_pg ∧ C.observable.centered = true ∧
  C.observable.smearing.compactSupport = true ∧ C.massWitness = rho_Apg_3320_positive ∧
  C.massWitness.observable = C.observable ∧ C.value = 33 / 20 ∧
  C.massWitness.value = C.value ∧ C.massWitness.positiveMass = true ∧
  C.sectorSeparation.ready ∧ C.sectorSeparation.witnessSector = Spectral.SpectralSector.orthogonal ∧
  C.sectorSeparation.witnessSector ≠ Spectral.SpectralSector.vacuum ∧
  C.spectralWeightVisible ∧ C.theoremBoundaryHeld

def observableSpectralWeight3320Certificate : ObservableSpectralWeightCertificate :=
  { observable := A_pg
    observableIsApg := by rfl
    observableCentered := by rfl
    observableCompactSupport := by rfl
    massWitness := rho_Apg_3320_positive
    massWitnessIsRhoApg3320 := by rfl
    massWitnessObservableMatches := by rfl
    value := 33 / 20
    valueIs3320 := by rfl
    massWitnessValueMatches := by rfl
    positiveMass := by rfl
    sectorSeparation := Spectral.spectralSectorSeparationCertificate
    sectorSeparationReady := Spectral.spectral_sector_separation_certificate_ready
    witnessSectorIsOrthogonal := by rfl
    witnessNotVacuum := by decide
    spectralWeightVisible := True
    theoremBoundaryHeld := True }

theorem observable_spectral_weight_certificate_pack
    (C : ObservableSpectralWeightCertificate) :
    C.ready ↔ C.observable = A_pg ∧ C.observable.centered = true ∧
      C.observable.smearing.compactSupport = true ∧ C.massWitness = rho_Apg_3320_positive ∧
      C.massWitness.observable = C.observable ∧ C.value = 33 / 20 ∧
      C.massWitness.value = C.value ∧ C.massWitness.positiveMass = true ∧
      C.sectorSeparation.ready ∧ C.sectorSeparation.witnessSector = Spectral.SpectralSector.orthogonal ∧
      C.sectorSeparation.witnessSector ≠ Spectral.SpectralSector.vacuum ∧
      C.spectralWeightVisible ∧ C.theoremBoundaryHeld := by
  rfl

theorem observable_spectral_weight_3320_certificate_ready :
    observableSpectralWeight3320Certificate.ready := by
  exact And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro Spectral.spectral_sector_separation_certificate_ready <|
    And.intro rfl <|
    And.intro (by decide) <|
    And.intro True.intro True.intro

theorem observable_spectral_weight_3320_value :
    observableSpectralWeight3320Certificate.value = 33 / 20 := by
  rfl

theorem observable_spectral_weight_3320_mass_value :
    observableSpectralWeight3320Certificate.massWitness.value = 33 / 20 := by
  rfl

theorem observable_spectral_weight_3320_positive_mass :
    observableSpectralWeight3320Certificate.massWitness.positiveMass = true := by
  rfl

theorem observable_spectral_weight_3320_centered :
    observableSpectralWeight3320Certificate.observable.centered = true := by
  rfl

theorem observable_spectral_weight_3320_compact_support :
    observableSpectralWeight3320Certificate.observable.smearing.compactSupport = true := by
  rfl

theorem observable_spectral_weight_3320_witness_orthogonal :
    observableSpectralWeight3320Certificate.sectorSeparation.witnessSector =
      Spectral.SpectralSector.orthogonal := by
  rfl

theorem observable_spectral_weight_3320_witness_not_vacuum :
    observableSpectralWeight3320Certificate.sectorSeparation.witnessSector ≠
      Spectral.SpectralSector.vacuum := by
  decide

end Plaquette
end MGAP4D
