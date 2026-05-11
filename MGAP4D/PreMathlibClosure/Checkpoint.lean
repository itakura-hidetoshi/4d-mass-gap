import MGAP4D.MathlibAdoptionGate.RequestRegistry
import MGAP4D.MathlibAdoptionGate.DryRunResultLedger
import MGAP4D.R1.Theorem.HilbertMilestone

namespace MGAP4D
namespace PreMathlibClosure

structure PreMathlibCheckpoint where
  theoremSurfacesReady : Prop
  replacementPassesClosed : Prop
  mathlibAdoptionGateReady : Prop
  requestRegistryReady : Prop
  r1HilbertMilestoneReady : Prop
  dryRunPathReady : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop

def PreMathlibCheckpoint.ready (C : PreMathlibCheckpoint) : Prop :=
  C.theoremSurfacesReady ∧ C.replacementPassesClosed ∧ C.mathlibAdoptionGateReady ∧
  C.requestRegistryReady ∧ C.r1HilbertMilestoneReady ∧ C.dryRunPathReady ∧
  C.statusSurfacesPreserved ∧ C.publicBoundaryHeld

theorem pre_mathlib_checkpoint_pack
    (C : PreMathlibCheckpoint) :
    C.ready ↔ C.theoremSurfacesReady ∧ C.replacementPassesClosed ∧ C.mathlibAdoptionGateReady ∧
      C.requestRegistryReady ∧ C.r1HilbertMilestoneReady ∧ C.dryRunPathReady ∧
      C.statusSurfacesPreserved ∧ C.publicBoundaryHeld := by
  rfl

end PreMathlibClosure
end MGAP4D
