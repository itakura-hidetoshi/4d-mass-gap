import MGAP4D.R2.TheoremSurface
import MGAP4D.R3.Concrete.ShiftedOperatorStatus

namespace MGAP4D
namespace R3
namespace TheoremSurface

structure ShiftedSurface where
  r2SurfaceReady : Prop
  shiftedStatusReady : Prop
  lowerInputReady : Prop
  shiftedDeclared : Prop
  nonnegativeSurface : Prop

def ShiftedSurface.ready (S : ShiftedSurface) : Prop :=
  S.r2SurfaceReady ∧ S.shiftedStatusReady ∧ S.lowerInputReady ∧
  S.shiftedDeclared ∧ S.nonnegativeSurface

theorem shifted_surface_pack
    (S : ShiftedSurface) :
    S.ready ↔ S.r2SurfaceReady ∧ S.shiftedStatusReady ∧ S.lowerInputReady ∧
      S.shiftedDeclared ∧ S.nonnegativeSurface := by
  rfl

end TheoremSurface
end R3
end MGAP4D
