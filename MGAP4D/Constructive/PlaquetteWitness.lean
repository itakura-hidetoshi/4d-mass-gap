import MGAP4D.Constructive.Gap3320
import MGAP4D.Plaquette.SpectralMeasure

namespace MGAP4D
namespace Constructive

/-- Minimal migration carrier for the plaquette spectral witness. -/
structure PlaquetteGapWitness where
  observableWitness : Plaquette.SpectralMassWitness
  gapRecord : MassGapRecord
  deriving Repr, DecidableEq

/-- Symbolic witness for positive mass of `A_{p,g}` at `33/20`. -/
def plaquetteGap3320Witness : PlaquetteGapWitness :=
  { observableWitness := Plaquette.rho_Apg_3320_positive,
    gapRecord := massGap3320 }

theorem plaquetteGap3320_value : plaquetteGap3320Witness.observableWitness.value = 33 / 20 := by
  rfl

theorem plaquetteGap3320_positiveMass : plaquetteGap3320Witness.observableWitness.positiveMass = true := by
  rfl

end Constructive
end MGAP4D
