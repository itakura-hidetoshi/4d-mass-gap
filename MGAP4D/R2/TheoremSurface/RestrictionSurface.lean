import MGAP4D.R2.TheoremSurface.ReducingSurface
import MGAP4D.R2.Concrete.SelfAdjointRestrictionStatus

namespace MGAP4D
namespace R2
namespace TheoremSurface

structure RestrictionSurface where
  reducingSurfaceReady : Prop
  restrictionStatusReady : Prop
  domainSurface : Prop
  selfAdjointSurface : Prop
  bindingDeferred : Prop

def RestrictionSurface.ready (S : RestrictionSurface) : Prop :=
  S.reducingSurfaceReady ∧ S.restrictionStatusReady ∧ S.domainSurface ∧
  S.selfAdjointSurface ∧ S.bindingDeferred

theorem restriction_surface_pack
    (S : RestrictionSurface) :
    S.ready ↔ S.reducingSurfaceReady ∧ S.restrictionStatusReady ∧ S.domainSurface ∧
      S.selfAdjointSurface ∧ S.bindingDeferred := by
  rfl

end TheoremSurface
end R2
end MGAP4D
