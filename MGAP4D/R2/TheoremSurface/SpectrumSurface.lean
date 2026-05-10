import MGAP4D.R2.TheoremSurface.ExcitedHamiltonianSurface
import MGAP4D.R2.Concrete.SpectrumUnionStatus

namespace MGAP4D
namespace R2
namespace TheoremSurface

structure SpectrumSurface where
  excitedHamiltonianSurfaceReady : Prop
  spectrumStatusReady : Prop
  vacuumSpectrumSurface : Prop
  excitedSpectrumSurface : Prop
  unionSurface : Prop

def SpectrumSurface.ready (S : SpectrumSurface) : Prop :=
  S.excitedHamiltonianSurfaceReady ∧ S.spectrumStatusReady ∧ S.vacuumSpectrumSurface ∧
  S.excitedSpectrumSurface ∧ S.unionSurface

theorem spectrum_surface_pack
    (S : SpectrumSurface) :
    S.ready ↔ S.excitedHamiltonianSurfaceReady ∧ S.spectrumStatusReady ∧ S.vacuumSpectrumSurface ∧
      S.excitedSpectrumSurface ∧ S.unionSurface := by
  rfl

end TheoremSurface
end R2
end MGAP4D
