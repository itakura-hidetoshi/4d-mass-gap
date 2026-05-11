import MGAP4D.R6.Concrete.IntervalCandidateBundle

namespace MGAP4D
namespace R6
namespace Concrete

structure IntervalTheoremChecklist where
  r5SideIdentified : Prop
  vacuumSideIdentified : Prop
  excitedSideIdentified : Prop
  intervalBoundaryIdentified : Prop
  exclusionTargetIdentified : Prop
  r6RequestRecorded : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop

def IntervalTheoremChecklist.ready (C : IntervalTheoremChecklist) : Prop :=
  C.r5SideIdentified ∧ C.vacuumSideIdentified ∧ C.excitedSideIdentified ∧
  C.intervalBoundaryIdentified ∧ C.exclusionTargetIdentified ∧ C.r6RequestRecorded ∧
  C.statusSurfacesPreserved ∧ C.publicBoundaryHeld

theorem interval_theorem_checklist_pack
    (C : IntervalTheoremChecklist) :
    C.ready ↔ C.r5SideIdentified ∧ C.vacuumSideIdentified ∧ C.excitedSideIdentified ∧
      C.intervalBoundaryIdentified ∧ C.exclusionTargetIdentified ∧ C.r6RequestRecorded ∧
      C.statusSurfacesPreserved ∧ C.publicBoundaryHeld := by
  rfl

end Concrete
end R6
end MGAP4D
