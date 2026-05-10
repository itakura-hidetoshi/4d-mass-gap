import MGAP4D.R3.TheoremSurface
import MGAP4D.R5.TheoremSurface
import MGAP4D.R7.Concrete.AtomPersistenceStatus

namespace MGAP4D
namespace R7
namespace TheoremSurface

structure AtomSurface where
  r3SurfaceReady : Prop
  r5SurfaceReady : Prop
  atomStatusReady : Prop
  atomRecorded : Prop
  persistenceSurface : Prop

def AtomSurface.ready (S : AtomSurface) : Prop :=
  S.r3SurfaceReady ∧ S.r5SurfaceReady ∧ S.atomStatusReady ∧
  S.atomRecorded ∧ S.persistenceSurface

theorem atom_surface_pack
    (S : AtomSurface) :
    S.ready ↔ S.r3SurfaceReady ∧ S.r5SurfaceReady ∧ S.atomStatusReady ∧
      S.atomRecorded ∧ S.persistenceSurface := by
  rfl

end TheoremSurface
end R7
end MGAP4D
