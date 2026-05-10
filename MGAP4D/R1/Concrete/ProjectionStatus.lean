import MGAP4D.R1.Concrete.InnerFunctionalStatus

namespace MGAP4D
namespace R1
namespace Concrete

structure ProjectionStatus where
  innerFunctionalReady : Prop
  closedKernelTargetRecorded : Prop
  vacuumProjectionPlanned : Prop
  excitedProjectionPlanned : Prop
  exportToR2Deferred : Prop

def ProjectionStatus.ready (S : ProjectionStatus) : Prop :=
  S.innerFunctionalReady ∧ S.closedKernelTargetRecorded ∧ S.vacuumProjectionPlanned ∧
  S.excitedProjectionPlanned ∧ S.exportToR2Deferred

theorem projection_status_pack
    (S : ProjectionStatus) :
    S.ready ↔ S.innerFunctionalReady ∧ S.closedKernelTargetRecorded ∧ S.vacuumProjectionPlanned ∧
      S.excitedProjectionPlanned ∧ S.exportToR2Deferred := by
  rfl

end Concrete
end R1
end MGAP4D
