import MGAP4D.R1.Concrete

namespace MGAP4D
namespace R2
namespace Concrete

structure ReducingSubspaceStatus where
  r1ProjectionReady : Prop
  vacuumProjectionCommutesPlanned : Prop
  excitedProjectionCommutesPlanned : Prop
  reducingSubspaceTargetRecorded : Prop
  mathlibBindingDeferred : Prop

def ReducingSubspaceStatus.ready (S : ReducingSubspaceStatus) : Prop :=
  S.r1ProjectionReady ∧ S.vacuumProjectionCommutesPlanned ∧
  S.excitedProjectionCommutesPlanned ∧ S.reducingSubspaceTargetRecorded ∧
  S.mathlibBindingDeferred

theorem reducing_subspace_status_pack
    (S : ReducingSubspaceStatus) :
    S.ready ↔ S.r1ProjectionReady ∧ S.vacuumProjectionCommutesPlanned ∧
      S.excitedProjectionCommutesPlanned ∧ S.reducingSubspaceTargetRecorded ∧
      S.mathlibBindingDeferred := by
  rfl

end Concrete
end R2
end MGAP4D
