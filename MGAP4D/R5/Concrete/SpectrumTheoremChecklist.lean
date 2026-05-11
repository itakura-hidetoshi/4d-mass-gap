import MGAP4D.R5.Concrete.SpectrumCandidateBundle

namespace MGAP4D
namespace R5
namespace Concrete

structure SpectrumTheoremChecklist where
  setIdentified : Prop
  bottomIdentified : Prop
  witnessIdentified : Prop
  comparisonIdentified : Prop
  targetIdentified : Prop
  r5RequestRecorded : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop

def SpectrumTheoremChecklist.ready (C : SpectrumTheoremChecklist) : Prop :=
  C.setIdentified ∧ C.bottomIdentified ∧ C.witnessIdentified ∧
  C.comparisonIdentified ∧ C.targetIdentified ∧ C.r5RequestRecorded ∧
  C.statusSurfacesPreserved ∧ C.publicBoundaryHeld

theorem spectrum_theorem_checklist_pack
    (C : SpectrumTheoremChecklist) :
    C.ready ↔ C.setIdentified ∧ C.bottomIdentified ∧ C.witnessIdentified ∧
      C.comparisonIdentified ∧ C.targetIdentified ∧ C.r5RequestRecorded ∧
      C.statusSurfacesPreserved ∧ C.publicBoundaryHeld := by
  rfl

end Concrete
end R5
end MGAP4D
