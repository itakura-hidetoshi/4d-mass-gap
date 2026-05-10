import MGAP4D.R1.Concrete.ExcitedSubspaceStatus

namespace MGAP4D
namespace R1
namespace Concrete

structure InnerFunctionalStatus where
  excitedSubspaceReady : Prop
  rawFunctionalPlanned : Prop
  boundednessRouteRecorded : Prop
  clmUpgradeTargetRecorded : Prop
  routeSelectionDeferred : Prop

def InnerFunctionalStatus.ready (S : InnerFunctionalStatus) : Prop :=
  S.excitedSubspaceReady ∧ S.rawFunctionalPlanned ∧ S.boundednessRouteRecorded ∧
  S.clmUpgradeTargetRecorded ∧ S.routeSelectionDeferred

theorem inner_functional_status_pack
    (S : InnerFunctionalStatus) :
    S.ready ↔ S.excitedSubspaceReady ∧ S.rawFunctionalPlanned ∧ S.boundednessRouteRecorded ∧
      S.clmUpgradeTargetRecorded ∧ S.routeSelectionDeferred := by
  rfl

end Concrete
end R1
end MGAP4D
