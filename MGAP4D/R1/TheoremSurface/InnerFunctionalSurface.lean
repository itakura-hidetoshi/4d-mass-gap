import MGAP4D.R1.TheoremSurface.ExcitedSurface
import MGAP4D.R1.Concrete.InnerFunctionalStatus

namespace MGAP4D
namespace R1
namespace TheoremSurface

structure InnerFunctionalSurface where
  excitedSurfaceReady : Prop
  innerFunctionalStatusReady : Prop
  rawFunctionalSurface : Prop
  boundednessSurface : Prop
  clmSurface : Prop

def InnerFunctionalSurface.ready (S : InnerFunctionalSurface) : Prop :=
  S.excitedSurfaceReady ∧ S.innerFunctionalStatusReady ∧ S.rawFunctionalSurface ∧
  S.boundednessSurface ∧ S.clmSurface

theorem inner_functional_surface_pack
    (S : InnerFunctionalSurface) :
    S.ready ↔ S.excitedSurfaceReady ∧ S.innerFunctionalStatusReady ∧ S.rawFunctionalSurface ∧
      S.boundednessSurface ∧ S.clmSurface := by
  rfl

end TheoremSurface
end R1
end MGAP4D
