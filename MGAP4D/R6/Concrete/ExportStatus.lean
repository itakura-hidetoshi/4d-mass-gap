import MGAP4D.R6.Concrete.GapIntervalStatus
import MGAP4D.R6.TheoremSurface

namespace MGAP4D
namespace R6
namespace Concrete

structure ExportStatus where
  intervalReady : Prop
  exportToGlobalReady : Prop
  reviewGateActive : Prop

def ExportStatus.ready (S : ExportStatus) : Prop :=
  S.intervalReady ∧ S.exportToGlobalReady ∧ S.reviewGateActive

theorem export_status_pack
    (S : ExportStatus) :
    S.ready ↔ S.intervalReady ∧ S.exportToGlobalReady ∧ S.reviewGateActive := by
  rfl

structure ExportSurfaceReady where
  statusReady : Prop
  r6SurfaceReady : Prop
  gateActive : Prop

def ExportSurfaceReady.ready (S : ExportSurfaceReady) : Prop :=
  S.statusReady ∧ S.r6SurfaceReady ∧ S.gateActive

theorem export_surface_ready_pack
    (S : ExportSurfaceReady) :
    S.ready ↔ S.statusReady ∧ S.r6SurfaceReady ∧ S.gateActive := by
  rfl

end Concrete
end R6
end MGAP4D
