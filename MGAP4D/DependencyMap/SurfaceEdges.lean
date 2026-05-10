import MGAP4D.DependencyMap.TheoremChain

namespace MGAP4D
namespace DependencyMap

structure SurfaceEdge where
  source : SurfaceLayer
  target : SurfaceLayer
  reason : String
  gateRequired : Bool
  deriving Repr, DecidableEq

def surfaceEdges : List SurfaceEdge := [
  { source := SurfaceLayer.r1, target := SurfaceLayer.r2, reason := "projection export", gateRequired := true },
  { source := SurfaceLayer.r2, target := SurfaceLayer.r4, reason := "excited Hamiltonian input", gateRequired := true },
  { source := SurfaceLayer.r4, target := SurfaceLayer.r3, reason := "lower bound to shifted route", gateRequired := true },
  { source := SurfaceLayer.r4, target := SurfaceLayer.r5, reason := "lower bound to spectrum route", gateRequired := true },
  { source := SurfaceLayer.r3, target := SurfaceLayer.r7, reason := "kernel route to exact surface", gateRequired := true },
  { source := SurfaceLayer.r5, target := SurfaceLayer.r6, reason := "spectrum route to interval exclusion", gateRequired := true },
  { source := SurfaceLayer.r5, target := SurfaceLayer.r7, reason := "spectrum route to atom surface", gateRequired := true },
  { source := SurfaceLayer.r6, target := SurfaceLayer.global, reason := "interval exclusion to global", gateRequired := true },
  { source := SurfaceLayer.r7, target := SurfaceLayer.global, reason := "exact surface to global", gateRequired := true }
]

theorem surfaceEdges_nonempty : surfaceEdges.length > 0 := by
  decide

end DependencyMap
end MGAP4D
