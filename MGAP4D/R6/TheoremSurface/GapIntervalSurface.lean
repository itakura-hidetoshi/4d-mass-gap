import MGAP4D.R5.TheoremSurface
import MGAP4D.R6.Concrete.GapIntervalStatus

namespace MGAP4D
namespace R6
namespace TheoremSurface

structure GapIntervalSurface where
  r5SurfaceReady : Prop
  intervalStatusReady : Prop
  vacuumSideSurface : Prop
  excitedSideSurface : Prop
  exclusionSurface : Prop

def GapIntervalSurface.ready (S : GapIntervalSurface) : Prop :=
  S.r5SurfaceReady ∧ S.intervalStatusReady ∧ S.vacuumSideSurface ∧
  S.excitedSideSurface ∧ S.exclusionSurface

theorem gap_interval_surface_pack
    (S : GapIntervalSurface) :
    S.ready ↔ S.r5SurfaceReady ∧ S.intervalStatusReady ∧ S.vacuumSideSurface ∧
      S.excitedSideSurface ∧ S.exclusionSurface := by
  rfl

end TheoremSurface
end R6
end MGAP4D
