import MGAP4D.R5.TheoremSurface.InfimumSurface
import MGAP4D.R5.Concrete.ExportStatus

namespace MGAP4D
namespace R5
namespace TheoremSurface

structure ExportSurface where
  spectrumReady : Prop
  bottomReady : Prop
  exportStatusReady : Prop
  r6Ready : Prop
  globalReady : Prop
  gateActive : Prop

/-- R5-specific export-surface readiness.

This intentionally avoids the shared short dot-name `ExportSurface.ready` under
the theorem-surface namespaces. -/
def r5_export_surface_ready (S : ExportSurface) : Prop :=
  S.spectrumReady ∧ S.bottomReady ∧ S.exportStatusReady ∧
  S.r6Ready ∧ S.globalReady ∧ S.gateActive

theorem r5_export_surface_pack
    (S : ExportSurface) :
    r5_export_surface_ready S ↔ S.spectrumReady ∧ S.bottomReady ∧ S.exportStatusReady ∧
      S.r6Ready ∧ S.globalReady ∧ S.gateActive := by
  rfl

structure R5TheoremSurface where
  spectrumSet : SpectrumSetSurface
  infimum : InfimumSurface
  exportSurface : ExportSurface

def R5TheoremSurface.ready (S : R5TheoremSurface) : Prop :=
  S.spectrumSet.ready ∧ S.infimum.ready ∧ r5_export_surface_ready S.exportSurface

theorem r5_theorem_surface_pack
    (S : R5TheoremSurface) :
    S.ready ↔ S.spectrumSet.ready ∧ S.infimum.ready ∧ r5_export_surface_ready S.exportSurface := by
  rfl

end TheoremSurface
end R5
end MGAP4D
