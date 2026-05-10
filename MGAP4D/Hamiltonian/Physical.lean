import MGAP4D.Hamiltonian.Basic
import MGAP4D.Spectral.Gap

namespace MGAP4D
namespace Hamiltonian

/-- Minimal migration-level relation between a Hamiltonian label and a spectral gap witness. -/
structure PhysicalGapRecord where
  hamiltonian : HamiltonianLabel
  witness : Spectral.GapWitness

def physicalGap3320Record : PhysicalGapRecord :=
  { hamiltonian := Hphys,
    witness := Spectral.gap3320Witness }

theorem physicalGap3320_value : physicalGap3320Record.witness.gap.value = 33 / 20 := by
  rfl

end Hamiltonian
end MGAP4D
