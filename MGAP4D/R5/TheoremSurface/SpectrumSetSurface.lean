import MGAP4D.R4.TheoremSurface
import MGAP4D.R5.Concrete.SpectrumSetStatus

namespace MGAP4D
namespace R5
namespace TheoremSurface

structure SpectrumSetSurface where
  r4SurfaceReady : Prop
  spectrumSetStatusReady : Prop
  excitedSpectrumSurface : Prop
  totalSpectrumSurface : Prop
  lowerSurface : Prop

def SpectrumSetSurface.ready (S : SpectrumSetSurface) : Prop :=
  S.r4SurfaceReady ∧ S.spectrumSetStatusReady ∧ S.excitedSpectrumSurface ∧
  S.totalSpectrumSurface ∧ S.lowerSurface

theorem spectrum_set_surface_pack
    (S : SpectrumSetSurface) :
    S.ready ↔ S.r4SurfaceReady ∧ S.spectrumSetStatusReady ∧ S.excitedSpectrumSurface ∧
      S.totalSpectrumSurface ∧ S.lowerSurface := by
  rfl

end TheoremSurface
end R5
end MGAP4D
