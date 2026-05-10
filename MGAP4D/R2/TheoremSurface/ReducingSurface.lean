import MGAP4D.R1.TheoremSurface
import MGAP4D.R2.Concrete.ReducingSubspaceStatus

namespace MGAP4D
namespace R2
namespace TheoremSurface

structure ReducingSurface where
  r1SurfaceReady : Prop
  reducingStatusReady : Prop
  vacuumReductionSurface : Prop
  excitedReductionSurface : Prop
  bindingDeferred : Prop

def ReducingSurface.ready (S : ReducingSurface) : Prop :=
  S.r1SurfaceReady ∧ S.reducingStatusReady ∧ S.vacuumReductionSurface ∧
  S.excitedReductionSurface ∧ S.bindingDeferred

theorem reducing_surface_pack
    (S : ReducingSurface) :
    S.ready ↔ S.r1SurfaceReady ∧ S.reducingStatusReady ∧ S.vacuumReductionSurface ∧
      S.excitedReductionSurface ∧ S.bindingDeferred := by
  rfl

end TheoremSurface
end R2
end MGAP4D
