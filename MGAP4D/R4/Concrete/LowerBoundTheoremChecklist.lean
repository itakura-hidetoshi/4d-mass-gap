import MGAP4D.R4.Concrete.LowerBoundCandidateBundle

namespace MGAP4D
namespace R4
namespace Concrete

structure LowerBoundTheoremChecklist where
  r2TargetIdentified : Prop
  ledgerIdentified : Prop
  constantIdentified : Prop
  theoremTargetIdentified : Prop
  bridgeTargetIdentified : Prop
  estimateTargetIdentified : Prop
  r4RequestRecorded : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop

def LowerBoundTheoremChecklist.ready (C : LowerBoundTheoremChecklist) : Prop :=
  C.r2TargetIdentified ∧ C.ledgerIdentified ∧ C.constantIdentified ∧
  C.theoremTargetIdentified ∧ C.bridgeTargetIdentified ∧ C.estimateTargetIdentified ∧
  C.r4RequestRecorded ∧ C.statusSurfacesPreserved ∧ C.publicBoundaryHeld

theorem lower_bound_theorem_checklist_pack
    (C : LowerBoundTheoremChecklist) :
    C.ready ↔ C.r2TargetIdentified ∧ C.ledgerIdentified ∧ C.constantIdentified ∧
      C.theoremTargetIdentified ∧ C.bridgeTargetIdentified ∧ C.estimateTargetIdentified ∧
      C.r4RequestRecorded ∧ C.statusSurfacesPreserved ∧ C.publicBoundaryHeld := by
  rfl

end Concrete
end R4
end MGAP4D
