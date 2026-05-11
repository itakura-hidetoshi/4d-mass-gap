import MGAP4D.R2.Concrete.RestrictionCandidateBundle

namespace MGAP4D
namespace R2
namespace Concrete

structure RestrictionTheoremChecklist where
  reducingSubspaceIdentified : Prop
  fullHamiltonianSelfAdjointTargetIdentified : Prop
  restrictionDomainIdentified : Prop
  restrictionOperatorTargetIdentified : Prop
  restrictionSelfAdjointTheoremTargetIdentified : Prop
  operatorAPIBridgeTargetIdentified : Prop
  r2RestrictionRequestRecorded : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop

def RestrictionTheoremChecklist.ready (C : RestrictionTheoremChecklist) : Prop :=
  C.reducingSubspaceIdentified ∧ C.fullHamiltonianSelfAdjointTargetIdentified ∧
  C.restrictionDomainIdentified ∧ C.restrictionOperatorTargetIdentified ∧
  C.restrictionSelfAdjointTheoremTargetIdentified ∧ C.operatorAPIBridgeTargetIdentified ∧
  C.r2RestrictionRequestRecorded ∧ C.statusSurfacesPreserved ∧ C.publicBoundaryHeld

theorem restriction_theorem_checklist_pack
    (C : RestrictionTheoremChecklist) :
    C.ready ↔ C.reducingSubspaceIdentified ∧ C.fullHamiltonianSelfAdjointTargetIdentified ∧
      C.restrictionDomainIdentified ∧ C.restrictionOperatorTargetIdentified ∧
      C.restrictionSelfAdjointTheoremTargetIdentified ∧ C.operatorAPIBridgeTargetIdentified ∧
      C.r2RestrictionRequestRecorded ∧ C.statusSurfacesPreserved ∧ C.publicBoundaryHeld := by
  rfl

end Concrete
end R2
end MGAP4D
