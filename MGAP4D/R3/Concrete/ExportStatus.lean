import MGAP4D.R3.Concrete.ZeroFormKernelStatus

namespace MGAP4D
namespace R3
namespace Concrete

structure ExportStatus where
  shiftedOperatorReady : Prop
  zeroFormKernelReady : Prop
  exportToR7Ready : Prop
  reviewGateActive : Prop

def ExportStatus.ready (S : ExportStatus) : Prop :=
  S.shiftedOperatorReady ∧ S.zeroFormKernelReady ∧ S.exportToR7Ready ∧ S.reviewGateActive

theorem export_status_pack
    (S : ExportStatus) :
    S.ready ↔ S.shiftedOperatorReady ∧ S.zeroFormKernelReady ∧ S.exportToR7Ready ∧ S.reviewGateActive := by
  rfl

end Concrete
end R3
end MGAP4D
