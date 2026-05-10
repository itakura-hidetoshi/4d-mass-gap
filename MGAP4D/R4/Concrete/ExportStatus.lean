import MGAP4D.R4.Concrete.OperatorBridgeStatus

namespace MGAP4D
namespace R4
namespace Concrete

structure ExportStatus where
  lowerBoundReady : Prop
  bridgeReady : Prop
  exportToR3Ready : Prop
  exportToR5Ready : Prop
  reviewGateActive : Prop

def ExportStatus.ready (S : ExportStatus) : Prop :=
  S.lowerBoundReady ∧ S.bridgeReady ∧ S.exportToR3Ready ∧ S.exportToR5Ready ∧ S.reviewGateActive

theorem export_status_pack
    (S : ExportStatus) :
    S.ready ↔ S.lowerBoundReady ∧ S.bridgeReady ∧ S.exportToR3Ready ∧ S.exportToR5Ready ∧ S.reviewGateActive := by
  rfl

end Concrete
end R4
end MGAP4D
