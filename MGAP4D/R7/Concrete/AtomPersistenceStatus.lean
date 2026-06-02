import MGAP4D.R3.Concrete.ExportStatus
import MGAP4D.R5.Concrete.ExportStatus

namespace MGAP4D
namespace R7
namespace Concrete

structure AtomPersistenceStatus where
  r3KernelReady : Prop
  r5SpectrumReady : Prop
  atomSurfaceRecorded : Prop
  noncollapseRecorded : Prop
  proofBindingDeferred : Prop

def AtomPersistenceStatus.ready (S : AtomPersistenceStatus) : Prop :=
  S.r3KernelReady ∧ S.r5SpectrumReady ∧ S.atomSurfaceRecorded ∧ S.noncollapseRecorded ∧ S.proofBindingDeferred

theorem atom_persistence_status_pack
    (S : AtomPersistenceStatus) :
    S.ready ↔ S.r3KernelReady ∧ S.r5SpectrumReady ∧ S.atomSurfaceRecorded ∧ S.noncollapseRecorded ∧ S.proofBindingDeferred := by
  rfl

end Concrete
end R7
end MGAP4D