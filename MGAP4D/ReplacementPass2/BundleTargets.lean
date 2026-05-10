import MGAP4D.ReplacementPass2.Gate

namespace MGAP4D
namespace ReplacementPass2

structure Pass2BundleTargets where
  operatorBundleReady : Prop
  r1ClosureBundleReady : Prop
  r2r4r3RouteBundleReady : Prop
  r5r6r7RouteBundleReady : Prop
  globalConcreteBundleReady : Prop
  finalAssemblyBundleReady : Prop

def Pass2BundleTargets.ready (B : Pass2BundleTargets) : Prop :=
  B.operatorBundleReady ∧ B.r1ClosureBundleReady ∧ B.r2r4r3RouteBundleReady ∧
  B.r5r6r7RouteBundleReady ∧ B.globalConcreteBundleReady ∧ B.finalAssemblyBundleReady

theorem pass2_bundle_targets_pack
    (B : Pass2BundleTargets) :
    B.ready ↔ B.operatorBundleReady ∧ B.r1ClosureBundleReady ∧ B.r2r4r3RouteBundleReady ∧
      B.r5r6r7RouteBundleReady ∧ B.globalConcreteBundleReady ∧ B.finalAssemblyBundleReady := by
  rfl

end ReplacementPass2
end MGAP4D
