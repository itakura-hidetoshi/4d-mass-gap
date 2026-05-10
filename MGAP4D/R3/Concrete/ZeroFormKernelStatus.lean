import MGAP4D.R3.Concrete.ShiftedOperatorStatus

namespace MGAP4D
namespace R3
namespace Concrete

structure ZeroFormKernelStatus where
  shiftedOperatorReady : Prop
  zeroFormConditionRecorded : Prop
  sqrtKernelRouteRecorded : Prop
  domainBridgeDeferred : Prop
  exportToR7Deferred : Prop

def ZeroFormKernelStatus.ready (S : ZeroFormKernelStatus) : Prop :=
  S.shiftedOperatorReady ∧ S.zeroFormConditionRecorded ∧ S.sqrtKernelRouteRecorded ∧
  S.domainBridgeDeferred ∧ S.exportToR7Deferred

theorem zero_form_kernel_status_pack
    (S : ZeroFormKernelStatus) :
    S.ready ↔ S.shiftedOperatorReady ∧ S.zeroFormConditionRecorded ∧
      S.sqrtKernelRouteRecorded ∧ S.domainBridgeDeferred ∧ S.exportToR7Deferred := by
  rfl

end Concrete
end R3
end MGAP4D
