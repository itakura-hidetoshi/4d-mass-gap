import MGAP4D.R2.Concrete.SpectrumUnionStatus
import MGAP4D.ReplacementCheckpoint

namespace MGAP4D
namespace R2
namespace Concrete

structure ExportStatus where
  reducingSubspaceReady : Prop
  selfAdjointRestrictionReady : Prop
  excitedHamiltonianReady : Prop
  spectrumUnionReady : Prop
  exportToR3Ready : Prop
  exportToR4Ready : Prop
  exportToR5Ready : Prop

def ExportStatus.ready (S : ExportStatus) : Prop :=
  S.reducingSubspaceReady ∧ S.selfAdjointRestrictionReady ∧
  S.excitedHamiltonianReady ∧ S.spectrumUnionReady ∧
  S.exportToR3Ready ∧ S.exportToR4Ready ∧ S.exportToR5Ready

theorem export_status_pack
    (S : ExportStatus) :
    S.ready ↔ S.reducingSubspaceReady ∧ S.selfAdjointRestrictionReady ∧
      S.excitedHamiltonianReady ∧ S.spectrumUnionReady ∧
      S.exportToR3Ready ∧ S.exportToR4Ready ∧ S.exportToR5Ready := by
  rfl

structure ExportSurfaceReady where
  statusReady : Prop
  r2SurfaceReady : Prop
  gateActive : Prop

def ExportSurfaceReady.ready (S : ExportSurfaceReady) : Prop :=
  S.statusReady ∧ S.r2SurfaceReady ∧ S.gateActive

theorem export_surface_ready_pack
    (S : ExportSurfaceReady) :
    S.ready ↔ S.statusReady ∧ S.r2SurfaceReady ∧ S.gateActive := by
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
end R2
end MGAP4D