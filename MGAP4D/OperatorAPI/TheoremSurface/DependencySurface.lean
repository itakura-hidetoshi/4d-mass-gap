import MGAP4D.OperatorAPI.BindingObligations
import MGAP4D.OperatorAPI.TheoremSurface.CandidateSurface

namespace MGAP4D
namespace OperatorAPI
namespace TheoremSurface

structure DependencySurface where
  candidateSurfaceReady : Prop
  r1DependencyReady : Prop
  r2DependencyReady : Prop
  r4DependencyReady : Prop
  r3DependencyReady : Prop
  r7DependencyReady : Prop
  globalDependencyReady : Prop

def DependencySurface.ready (S : DependencySurface) : Prop :=
  S.candidateSurfaceReady ∧ S.r1DependencyReady ∧ S.r2DependencyReady ∧
  S.r4DependencyReady ∧ S.r3DependencyReady ∧ S.r7DependencyReady ∧
  S.globalDependencyReady

theorem dependency_surface_pack
    (S : DependencySurface) :
    S.ready ↔ S.candidateSurfaceReady ∧ S.r1DependencyReady ∧ S.r2DependencyReady ∧
      S.r4DependencyReady ∧ S.r3DependencyReady ∧ S.r7DependencyReady ∧
      S.globalDependencyReady := by
  rfl

structure DependencyOrderSurface where
  r1BeforeR2 : Prop
  r2BeforeR4 : Prop
  r4BeforeR3 : Prop
  r3BeforeR7 : Prop
  r7BeforeGlobal : Prop

def DependencyOrderSurface.ready (S : DependencyOrderSurface) : Prop :=
  S.r1BeforeR2 ∧ S.r2BeforeR4 ∧ S.r4BeforeR3 ∧ S.r3BeforeR7 ∧ S.r7BeforeGlobal

theorem dependency_order_surface_pack
    (S : DependencyOrderSurface) :
    S.ready ↔ S.r1BeforeR2 ∧ S.r2BeforeR4 ∧ S.r4BeforeR3 ∧ S.r3BeforeR7 ∧ S.r7BeforeGlobal := by
  rfl

end TheoremSurface
end OperatorAPI
end MGAP4D
