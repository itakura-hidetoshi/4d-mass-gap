import MGAP4D.R6.TheoremSurface.GapIntervalSurface
import MGAP4D.R6.Concrete.ExportStatus

namespace MGAP4D
namespace R6
namespace TheoremSurface

structure ExportSurface where
  intervalReady : Prop
  exportStatusReady : Prop
  globalReady : Prop
  gateActive : Prop

/-- R6-specific export-surface readiness.

This intentionally avoids the shared short dot-name `ExportSurface.ready` under
the theorem-surface namespaces. -/
def r6_export_surface_ready (S : ExportSurface) : Prop :=
  S.intervalReady ∧ S.exportStatusReady ∧ S.globalReady ∧ S.gateActive

theorem r6_export_surface_pack
    (S : ExportSurface) :
    r6_export_surface_ready S ↔ S.intervalReady ∧ S.exportStatusReady ∧ S.globalReady ∧ S.gateActive := by
  rfl

structure R6TheoremSurface where
  interval : GapIntervalSurface
  exportSurface : ExportSurface

def R6TheoremSurface.ready (S : R6TheoremSurface) : Prop :=
  S.interval.ready ∧ r6_export_surface_ready S.exportSurface

theorem r6_theorem_surface_pack
    (S : R6TheoremSurface) :
    S.ready ↔ S.interval.ready ∧ r6_export_surface_ready S.exportSurface := by
  rfl

end TheoremSurface
end R6
end MGAP4D
