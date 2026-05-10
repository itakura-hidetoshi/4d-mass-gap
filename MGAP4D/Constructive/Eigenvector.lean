import MGAP4D.Constructive.Gap3320
import MGAP4D.Hamiltonian.Physical

namespace MGAP4D
namespace Constructive

/-- Minimal migration carrier for the eigenvector witness `psi_*`. -/
structure EigenvectorWitness where
  name : String
  normOne : Bool
  eigenvalue : Rat
  gapRecord : MassGapRecord
  deriving Repr, DecidableEq

/-- Symbolic witness for `psi_*` with eigenvalue `33/20`. -/
def psiStarWitness : EigenvectorWitness :=
  { name := "psi_*",
    normOne := true,
    eigenvalue := 33 / 20,
    gapRecord := massGap3320 }

theorem psiStar_normOne : psiStarWitness.normOne = true := by
  rfl

theorem psiStar_eigenvalue : psiStarWitness.eigenvalue = 33 / 20 := by
  rfl

end Constructive
end MGAP4D
