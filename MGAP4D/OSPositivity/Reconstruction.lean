import MGAP4D.OSPositivity.Reflection
import MGAP4D.Hamiltonian.Physical

namespace MGAP4D
namespace OSPositivity

/-- Minimal carrier connecting OS reflection data to a reconstructed physical gap record. -/
structure ReconstructionRecord where
  reflection : ReflectionRecord
  physicalGap : Hamiltonian.PhysicalGapRecord

def baselineReconstructionRecord : ReconstructionRecord :=
  { reflection := baselineReflectionRecord,
    physicalGap := Hamiltonian.physicalGap3320Record }

theorem baselineReconstruction_gap :
    baselineReconstructionRecord.physicalGap.witness.gap.value = 33 / 20 := by
  rfl

end OSPositivity
end MGAP4D
