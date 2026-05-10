import MGAP4D.Global.TheoremSurface.ReviewSurface

namespace MGAP4D
namespace Global
namespace TheoremSurface

structure FinalSurface where
  assembly : AssemblySurface
  review : ReviewSurface
  theoremSurfaceReady : Prop
  publicBoundaryHeld : Prop

def FinalSurface.ready (S : FinalSurface) : Prop :=
  S.assembly.ready ∧ S.review.ready ∧ S.theoremSurfaceReady ∧ S.publicBoundaryHeld

theorem final_surface_pack
    (S : FinalSurface) :
    S.ready ↔ S.assembly.ready ∧ S.review.ready ∧ S.theoremSurfaceReady ∧ S.publicBoundaryHeld := by
  rfl

end TheoremSurface
end Global
end MGAP4D
