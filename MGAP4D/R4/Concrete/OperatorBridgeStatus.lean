import MGAP4D.R4.Concrete.LowerBoundReceiptStatus

namespace MGAP4D
namespace R4
namespace Concrete

structure OperatorBridgeStatus where
  lowerBoundReady : Prop
  formBridgeRecorded : Prop
  r3ExportRecorded : Prop
  r5ExportRecorded : Prop
  closureDeferred : Prop

def OperatorBridgeStatus.ready (S : OperatorBridgeStatus) : Prop :=
  S.lowerBoundReady ∧ S.formBridgeRecorded ∧ S.r3ExportRecorded ∧ S.r5ExportRecorded ∧ S.closureDeferred

theorem operator_bridge_status_pack
    (S : OperatorBridgeStatus) :
    S.ready ↔ S.lowerBoundReady ∧ S.formBridgeRecorded ∧ S.r3ExportRecorded ∧ S.r5ExportRecorded ∧ S.closureDeferred := by
  rfl

end Concrete
end R4
end MGAP4D
