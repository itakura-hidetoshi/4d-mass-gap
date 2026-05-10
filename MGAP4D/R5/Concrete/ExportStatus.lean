import MGAP4D.R5.Concrete.InfimumStatus
import MGAP4D.R5.TheoremSurface
import MGAP4D.ReplacementCheckpoint

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
end R5
end MGAP4D
