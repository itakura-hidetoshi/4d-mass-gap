import MGAP4D.R1.TheoremSurface.HilbertSurface
import MGAP4D.R1.Concrete.ExcitedSubspaceStatus

namespace MGAP4D
namespace R1
namespace TheoremSurface

structure ExcitedSurface where
  hilbertSurfaceReady : Prop
  excitedStatusReady : Prop
  vacuumLineSurface : Prop
  excitedSubspaceSurface : Prop
  closednessSurface : Prop

def ExcitedSurface.ready (S : ExcitedSurface) : Prop :=
  S.hilbertSurfaceReady ∧ S.excitedStatusReady ∧ S.vacuumLineSurface ∧
  S.excitedSubspaceSurface ∧ S.closednessSurface

theorem excited_surface_pack
    (S : ExcitedSurface) :
    S.ready ↔ S.hilbertSurfaceReady ∧ S.excitedStatusReady ∧ S.vacuumLineSurface ∧
      S.excitedSubspaceSurface ∧ S.closednessSurface := by
  rfl

end TheoremSurface
end R1
end MGAP4D
