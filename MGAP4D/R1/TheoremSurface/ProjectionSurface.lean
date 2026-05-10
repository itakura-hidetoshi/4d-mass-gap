import MGAP4D.R1.TheoremSurface.InnerFunctionalSurface
import MGAP4D.R1.Concrete.ProjectionStatus

namespace MGAP4D
namespace R1
namespace TheoremSurface

structure ProjectionSurface where
  innerFunctionalSurfaceReady : Prop
  projectionStatusReady : Prop
  kernelSurface : Prop
  vacuumProjectionSurface : Prop
  excitedProjectionSurface : Prop

def ProjectionSurface.ready (S : ProjectionSurface) : Prop :=
  S.innerFunctionalSurfaceReady ∧ S.projectionStatusReady ∧ S.kernelSurface ∧
  S.vacuumProjectionSurface ∧ S.excitedProjectionSurface

theorem projection_surface_pack
    (S : ProjectionSurface) :
    S.ready ↔ S.innerFunctionalSurfaceReady ∧ S.projectionStatusReady ∧ S.kernelSurface ∧
      S.vacuumProjectionSurface ∧ S.excitedProjectionSurface := by
  rfl

end TheoremSurface
end R1
end MGAP4D
