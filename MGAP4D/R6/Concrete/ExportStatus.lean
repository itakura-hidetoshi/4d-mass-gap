import MGAP4D.R6.Concrete.GapIntervalStatus
import MGAP4D.ReplacementCheckpoint

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

structure ExportReplacementReady where
  exportSurfaceReady : Prop
  replacementGateReady : Prop
  statusPreserved : Prop

def ExportReplacementReady.ready (S : ExportReplacementReady) : Prop :=
  S.exportSurfaceReady ∧ S.replacementGateReady ∧ S.statusPreserved

theorem export_replacement_ready_pack
    (S : ExportReplacementReady) :
    S.ready ↔ S.exportSurfaceReady ∧ S.replacementGateReady ∧ S.statusPreserved := by
  rfl

end Concrete
end R6
end MGAP4D