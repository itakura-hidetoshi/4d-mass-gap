import MGAP4D.R1.Concrete.HilbertScaffoldStatus

namespace MGAP4D
namespace R1
namespace Concrete

structure ExcitedSubspaceStatus where
  hilbertScaffoldReady : Prop
  vacuumLinePlanned : Prop
  excitedSubspacePlanned : Prop
  closedSubspaceTargetRecorded : Prop
  projectionExportDeferred : Prop

def ExcitedSubspaceStatus.ready (S : ExcitedSubspaceStatus) : Prop :=
  S.hilbertScaffoldReady ∧ S.vacuumLinePlanned ∧ S.excitedSubspacePlanned ∧
  S.closedSubspaceTargetRecorded ∧ S.projectionExportDeferred

theorem excited_subspace_status_pack
    (S : ExcitedSubspaceStatus) :
    S.ready ↔ S.hilbertScaffoldReady ∧ S.vacuumLinePlanned ∧ S.excitedSubspacePlanned ∧
      S.closedSubspaceTargetRecorded ∧ S.projectionExportDeferred := by
  rfl

end Concrete
end R1
end MGAP4D
