import MGAP4D.R5.Concrete.InfimumStatus
import MGAP4D.R5.TheoremSurface

namespace MGAP4D
namespace R5
namespace Concrete

structure ExportStatus where
  spectrumReady : Prop
  bottomReady : Prop
  exportToR6Ready : Prop
  exportToGlobalReady : Prop
  reviewGateActive : Prop

def ExportStatus.ready (S : ExportStatus) : Prop :=
  S.spectrumReady ∧ S.bottomReady ∧ S.exportToR6Ready ∧ S.exportToGlobalReady ∧ S.reviewGateActive

theorem export_status_pack
    (S : ExportStatus) :
    S.ready ↔ S.spectrumReady ∧ S.bottomReady ∧ S.exportToR6Ready ∧ S.exportToGlobalReady ∧ S.reviewGateActive := by
  rfl

structure ExportSurfaceReady where
  statusReady : Prop
  r5SurfaceReady : Prop
  gateActive : Prop

def ExportSurfaceReady.ready (S : ExportSurfaceReady) : Prop :=
  S.statusReady ∧ S.r5SurfaceReady ∧ S.gateActive

theorem export_surface_ready_pack
    (S : ExportSurfaceReady) :
    S.ready ↔ S.statusReady ∧ S.r5SurfaceReady ∧ S.gateActive := by
  rfl

end Concrete
end R5
end MGAP4D
