import MGAP4D.R6.TheoremSurface
import MGAP4D.R7.TheoremSurface

namespace MGAP4D
namespace Global
namespace TheoremSurface

structure AssemblySurface where
  r6SurfaceReady : Prop
  r7SurfaceReady : Prop
  gapIntervalReady : Prop
  exactGapReady : Prop
  assemblyReady : Prop

def AssemblySurface.ready (S : AssemblySurface) : Prop :=
  S.r6SurfaceReady ∧ S.r7SurfaceReady ∧ S.gapIntervalReady ∧
  S.exactGapReady ∧ S.assemblyReady

theorem assembly_surface_pack
    (S : AssemblySurface) :
    S.ready ↔ S.r6SurfaceReady ∧ S.r7SurfaceReady ∧ S.gapIntervalReady ∧
      S.exactGapReady ∧ S.assemblyReady := by
  rfl

end TheoremSurface
end Global
end MGAP4D
