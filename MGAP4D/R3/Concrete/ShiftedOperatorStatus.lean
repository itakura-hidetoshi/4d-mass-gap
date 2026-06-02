import MGAP4D.R2.Concrete.ExcitedHamiltonianStatus

namespace MGAP4D
namespace R3
namespace Concrete

structure ShiftedOperatorStatus where
  r2ExcitedHamiltonianReady : Prop
  lowerBoundInputDeferred : Prop
  shiftedOperatorDeclared : Prop
  nonnegativeTargetRecorded : Prop
  sqrtRouteDeferred : Prop

def ShiftedOperatorStatus.ready (S : ShiftedOperatorStatus) : Prop :=
  S.r2ExcitedHamiltonianReady ∧ S.lowerBoundInputDeferred ∧
  S.shiftedOperatorDeclared ∧ S.nonnegativeTargetRecorded ∧ S.sqrtRouteDeferred

theorem shifted_operator_status_pack
    (S : ShiftedOperatorStatus) :
    S.ready ↔ S.r2ExcitedHamiltonianReady ∧ S.lowerBoundInputDeferred ∧
      S.shiftedOperatorDeclared ∧ S.nonnegativeTargetRecorded ∧ S.sqrtRouteDeferred := by
  rfl

end Concrete
end R3
end MGAP4D