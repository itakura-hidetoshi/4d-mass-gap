import MGAP4D.R4.Concrete.OperatorBridgeStatus
import MGAP4D.R4.TheoremSurface

namespace MGAP4D
namespace R4
namespace Concrete

structure ExportStatus where
  lowerBoundReady : Prop
  bridgeReady : Prop
  exportToR3Ready : Prop
  exportToR5Ready : Prop
  reviewGateActive : Prop

def ExportStatus.ready (S : ExportStatus) : Prop :=
  S.lowerBoundReady ∧ S.bridgeReady ∧ S.exportToR3Ready ∧ S.exportToR5Ready ∧ S.reviewGateActive

theorem export_status_pack
    (S : ExportStatus) :
    S.ready ↔ S.lowerBoundReady ∧ S.bridgeReady ∧ S.exportToR3Ready ∧ S.exportToR5Ready ∧ S.reviewGateActive := by
  rfl

structure ExportSurfaceReady where
  statusReady : Prop
  r4SurfaceReady : Prop
  gateActive : Prop

def ExportSurfaceReady.ready (S : ExportSurfaceReady) : Prop :=
  S.statusReady ∧ S.r4SurfaceReady ∧ S.gateActive

theorem export_surface_ready_pack
    (S : ExportSurfaceReady) :
    S.ready ↔ S.statusReady ∧ S.r4SurfaceReady ∧ S.gateActive := by
  rfl

end Concrete
end R4
end MGAP4D
