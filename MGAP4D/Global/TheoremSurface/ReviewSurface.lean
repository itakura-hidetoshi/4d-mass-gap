import MGAP4D.Global.TheoremSurface.AssemblySurface

namespace MGAP4D
namespace Global
namespace TheoremSurface

structure ReviewSurface where
  assemblyReady : Prop
  ciGateReady : Prop
  auditGateReady : Prop
  replayGateReady : Prop
  publicGateActive : Prop

def ReviewSurface.ready (S : ReviewSurface) : Prop :=
  S.assemblyReady ∧ S.ciGateReady ∧ S.auditGateReady ∧
  S.replayGateReady ∧ S.publicGateActive

theorem review_surface_pack
    (S : ReviewSurface) :
    S.ready ↔ S.assemblyReady ∧ S.ciGateReady ∧ S.auditGateReady ∧
      S.replayGateReady ∧ S.publicGateActive := by
  rfl

end TheoremSurface
end Global
end MGAP4D
