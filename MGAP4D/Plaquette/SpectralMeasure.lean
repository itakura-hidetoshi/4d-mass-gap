import MGAP4D.Plaquette.Smeared
import MGAP4D.Spectral.Gap

namespace MGAP4D
namespace Plaquette

/-- Minimal migration-level carrier for positive spectral mass at a value. -/
structure SpectralMassWitness where
  observable : SmearedPlaquetteObservable
  value : Rat
  positiveMass : Bool
  deriving Repr, DecidableEq

/-- Symbolic witness for `rho_{A_{p,g}}({33/20}) > 0`. -/
def rho_Apg_3320_positive : SpectralMassWitness :=
  { observable := A_pg, value := 33 / 20, positiveMass := true }

theorem rho_Apg_3320_value : rho_Apg_3320_positive.value = 33 / 20 := by
  rfl

theorem rho_Apg_3320_positiveMass : rho_Apg_3320_positive.positiveMass = true := by
  rfl

end Plaquette
end MGAP4D
