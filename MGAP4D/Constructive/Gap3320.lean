import MGAP4D.Spectral.Gap
import MGAP4D.Hamiltonian.Physical

namespace MGAP4D
namespace Constructive

/-- Migration-level record for the normalized mass-gap value. -/
structure MassGapRecord where
  value : Rat
  spectralWitness : Spectral.GapWitness

def massGap3320 : MassGapRecord :=
  { value := 33 / 20,
    spectralWitness := Spectral.gap3320Witness }

theorem massGap3320_value : massGap3320.value = 33 / 20 := by
  rfl

theorem massGap3320_spectral_value : massGap3320.spectralWitness.gap.value = 33 / 20 := by
  rfl

end Constructive
end MGAP4D
