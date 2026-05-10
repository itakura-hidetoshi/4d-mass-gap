import MGAP4D.R6.Concrete.GapIntervalStatus

namespace MGAP4D
namespace R6
namespace Concrete

structure ExportStatus where
  intervalReady : Prop
  exportToGlobalReady : Prop
  reviewGateActive : Prop

def ExportStatus.ready (S : ExportStatus) : Prop :=
  S.intervalReady ∧ S.exportToGlobalReady ∧ S.reviewGateActive

theorem export_status_pack
    (S : ExportStatus) :
    S.ready ↔ S.intervalReady ∧ S.exportToGlobalReady ∧ S.reviewGateActive := by
  rfl

end Concrete
end R6
end MGAP4D
