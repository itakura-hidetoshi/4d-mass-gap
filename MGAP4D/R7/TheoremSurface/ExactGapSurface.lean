import MGAP4D.R7.TheoremSurface.AtomSurface
import MGAP4D.R7.Concrete.ExactGapStatus

namespace MGAP4D
namespace R7
namespace TheoremSurface

structure ExactGapSurface where
  atomSurfaceReady : Prop
  exactGapStatusReady : Prop
  eigenstateSurface : Prop
  exactGapSurface : Prop
  exportReady : Prop

def ExactGapSurface.ready (S : ExactGapSurface) : Prop :=
  S.atomSurfaceReady ∧ S.exactGapStatusReady ∧ S.eigenstateSurface ∧
  S.exactGapSurface ∧ S.exportReady

theorem exact_gap_surface_pack
    (S : ExactGapSurface) :
    S.ready ↔ S.atomSurfaceReady ∧ S.exactGapStatusReady ∧ S.eigenstateSurface ∧
      S.exactGapSurface ∧ S.exportReady := by
  rfl

end TheoremSurface
end R7
end MGAP4D
