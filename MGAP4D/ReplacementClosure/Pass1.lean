import MGAP4D.ReplacementCheckpoint

namespace MGAP4D
namespace ReplacementClosure

structure Pass1Closure where
  operatorAPIReady : Prop
  r1ClosureReady : Prop
  r2ExportReady : Prop
  r4ExportReady : Prop
  r3ExportReady : Prop
  r5ExportReady : Prop
  r6ExportReady : Prop
  r7ExactReady : Prop
  globalConcreteReady : Prop
  finalAssemblyReady : Prop

def Pass1Closure.ready (P : Pass1Closure) : Prop :=
  P.operatorAPIReady ∧ P.r1ClosureReady ∧ P.r2ExportReady ∧ P.r4ExportReady ∧
  P.r3ExportReady ∧ P.r5ExportReady ∧ P.r6ExportReady ∧ P.r7ExactReady ∧
  P.globalConcreteReady ∧ P.finalAssemblyReady

theorem pass1_closure_pack
    (P : Pass1Closure) :
    P.ready ↔ P.operatorAPIReady ∧ P.r1ClosureReady ∧ P.r2ExportReady ∧ P.r4ExportReady ∧
      P.r3ExportReady ∧ P.r5ExportReady ∧ P.r6ExportReady ∧ P.r7ExactReady ∧
      P.globalConcreteReady ∧ P.finalAssemblyReady := by
  rfl

end ReplacementClosure
end MGAP4D
