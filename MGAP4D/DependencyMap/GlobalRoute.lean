import MGAP4D.DependencyMap.SurfaceEdges

namespace MGAP4D
namespace DependencyMap

structure GlobalRoute where
  chainPresent : Prop
  edgesPresent : Prop
  r6ToGlobal : Prop
  r7ToGlobal : Prop
  finalSurfaceReady : Prop
  reviewGateActive : Prop

def GlobalRoute.ready (G : GlobalRoute) : Prop :=
  G.chainPresent ∧ G.edgesPresent ∧ G.r6ToGlobal ∧ G.r7ToGlobal ∧
  G.finalSurfaceReady ∧ G.reviewGateActive

theorem global_route_pack
    (G : GlobalRoute) :
    G.ready ↔ G.chainPresent ∧ G.edgesPresent ∧ G.r6ToGlobal ∧ G.r7ToGlobal ∧
      G.finalSurfaceReady ∧ G.reviewGateActive := by
  rfl

end DependencyMap
end MGAP4D
