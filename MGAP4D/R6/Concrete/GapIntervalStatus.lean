import MGAP4D.R5.Concrete.ExportStatus

namespace MGAP4D
namespace R6
namespace Concrete

structure GapIntervalStatus where
  r5Ready : Prop
  vacuumSideRecorded : Prop
  excitedSideRecorded : Prop
  intervalExclusionRecorded : Prop
  proofBindingDeferred : Prop

def GapIntervalStatus.ready (S : GapIntervalStatus) : Prop :=
  S.r5Ready ∧ S.vacuumSideRecorded ∧ S.excitedSideRecorded ∧ S.intervalExclusionRecorded ∧ S.proofBindingDeferred

theorem gap_interval_status_pack
    (S : GapIntervalStatus) :
    S.ready ↔ S.r5Ready ∧ S.vacuumSideRecorded ∧ S.excitedSideRecorded ∧ S.intervalExclusionRecorded ∧ S.proofBindingDeferred := by
  rfl

end Concrete
end R6
end MGAP4D