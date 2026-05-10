import MGAP4D.Constructive.Eigenvector
import MGAP4D.Constructive.PlaquetteWitness
import MGAP4D.OSPositivity.Reconstruction

namespace MGAP4D
namespace Constructive

/-- Migration-level top theorem packet for the MGAP4D `33/20` spine. -/
structure FinalTheoremPacket where
  massGap : MassGapRecord
  eigenvector : EigenvectorWitness
  plaquette : PlaquetteGapWitness
  reconstruction : OSPositivity.ReconstructionRecord

def finalTheoremPacket3320 : FinalTheoremPacket :=
  { massGap := massGap3320,
    eigenvector := psiStarWitness,
    plaquette := plaquetteGap3320Witness,
    reconstruction := OSPositivity.baselineReconstructionRecord }

theorem finalTheorem_massGap3320 : finalTheoremPacket3320.massGap.value = 33 / 20 := by
  rfl

theorem finalTheorem_eigenvalue3320 : finalTheoremPacket3320.eigenvector.eigenvalue = 33 / 20 := by
  rfl

theorem finalTheorem_plaquettePositive :
    finalTheoremPacket3320.plaquette.observableWitness.positiveMass = true := by
  rfl

end Constructive
end MGAP4D
