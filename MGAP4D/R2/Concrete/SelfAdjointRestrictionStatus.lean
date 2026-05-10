import MGAP4D.R2.Concrete.ReducingSubspaceStatus

namespace MGAP4D
namespace R2
namespace Concrete

structure SelfAdjointRestrictionStatus where
  reducingSubspaceReady : Prop
  fullHamiltonianSelfAdjointPlanned : Prop
  restrictionDomainPlanned : Prop
  restrictionSelfAdjointTargetRecorded : Prop
  operatorAPIBindingDeferred : Prop

def SelfAdjointRestrictionStatus.ready (S : SelfAdjointRestrictionStatus) : Prop :=
  S.reducingSubspaceReady ∧ S.fullHamiltonianSelfAdjointPlanned ∧
  S.restrictionDomainPlanned ∧ S.restrictionSelfAdjointTargetRecorded ∧
  S.operatorAPIBindingDeferred

theorem self_adjoint_restriction_status_pack
    (S : SelfAdjointRestrictionStatus) :
    S.ready ↔ S.reducingSubspaceReady ∧ S.fullHamiltonianSelfAdjointPlanned ∧
      S.restrictionDomainPlanned ∧ S.restrictionSelfAdjointTargetRecorded ∧
      S.operatorAPIBindingDeferred := by
  rfl

end Concrete
end R2
end MGAP4D
