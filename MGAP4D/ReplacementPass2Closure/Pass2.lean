import MGAP4D.ReplacementPass2
import MGAP4D.Global.FinalAssemblyPass2Bundle

namespace MGAP4D
namespace ReplacementPass2Closure

structure Pass2Closure where
  operatorBundleReady : Prop
  r1ClosureBundleReady : Prop
  r2r4r3RouteBundleReady : Prop
  r5r6r7RouteBundleReady : Prop
  globalConcreteBundleReady : Prop
  finalAssemblyBundleReady : Prop

def Pass2Closure.ready (P : Pass2Closure) : Prop :=
  P.operatorBundleReady ∧ P.r1ClosureBundleReady ∧ P.r2r4r3RouteBundleReady ∧
  P.r5r6r7RouteBundleReady ∧ P.globalConcreteBundleReady ∧ P.finalAssemblyBundleReady

theorem pass2_closure_pack
    (P : Pass2Closure) :
    P.ready ↔ P.operatorBundleReady ∧ P.r1ClosureBundleReady ∧ P.r2r4r3RouteBundleReady ∧
      P.r5r6r7RouteBundleReady ∧ P.globalConcreteBundleReady ∧ P.finalAssemblyBundleReady := by
  rfl

end ReplacementPass2Closure
end MGAP4D
