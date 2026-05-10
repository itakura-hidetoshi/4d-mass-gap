import MGAP4D.Spectral.Basic

namespace MGAP4D
namespace Hamiltonian

/-- Minimal carrier for a normalized Hamiltonian label during migration. -/
structure HamiltonianLabel where
  name : String
  deriving Repr, DecidableEq

/-- The physical Hamiltonian label used by the MGAP4D proof spine. -/
def Hphys : HamiltonianLabel :=
  { name := "H_phys" }

end Hamiltonian
end MGAP4D
