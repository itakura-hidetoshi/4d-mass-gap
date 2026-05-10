import MGAP4D.R2.TheoremSurface
import MGAP4D.R4.Concrete.LowerBoundReceiptStatus

namespace MGAP4D
namespace R4
namespace TheoremSurface

structure LowerBoundSurface where
  r2SurfaceReady : Prop
  receiptStatusReady : Prop
  decompositionSurface : Prop
  rationalConstantSurface : Prop
  lowerBoundSurface : Prop

def LowerBoundSurface.ready (S : LowerBoundSurface) : Prop :=
  S.r2SurfaceReady ∧ S.receiptStatusReady ∧ S.decompositionSurface ∧
  S.rationalConstantSurface ∧ S.lowerBoundSurface

theorem lower_bound_surface_pack
    (S : LowerBoundSurface) :
    S.ready ↔ S.r2SurfaceReady ∧ S.receiptStatusReady ∧ S.decompositionSurface ∧
      S.rationalConstantSurface ∧ S.lowerBoundSurface := by
  rfl

end TheoremSurface
end R4
end MGAP4D
