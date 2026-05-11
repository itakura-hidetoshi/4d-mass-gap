import MGAP4D.PreMathlibClosure.Checkpoint

namespace MGAP4D
namespace PreMathlibClosure

structure PreMathlibMainInvariant where
  lakefileUnchangedForMathlib : Prop
  noActiveMathlibImports : Prop
  dryRunIsBranchOnly : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop
  failureLedgerRequired : Prop

def PreMathlibMainInvariant.ready (I : PreMathlibMainInvariant) : Prop :=
  I.lakefileUnchangedForMathlib ∧ I.noActiveMathlibImports ∧ I.dryRunIsBranchOnly ∧
  I.statusSurfacesPreserved ∧ I.publicBoundaryHeld ∧ I.failureLedgerRequired

theorem pre_mathlib_main_invariant_pack
    (I : PreMathlibMainInvariant) :
    I.ready ↔ I.lakefileUnchangedForMathlib ∧ I.noActiveMathlibImports ∧ I.dryRunIsBranchOnly ∧
      I.statusSurfacesPreserved ∧ I.publicBoundaryHeld ∧ I.failureLedgerRequired := by
  rfl

end PreMathlibClosure
end MGAP4D
