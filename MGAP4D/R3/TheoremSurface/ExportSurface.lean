import MGAP4D.R3.TheoremSurface.ZeroFormSurface
import MGAP4D.R3.Concrete.ExportStatus

namespace MGAP4D
namespace R3
namespace TheoremSurface

structure ExportSurface where
  shiftedReady : Prop
  kernelRouteReady : Prop
  exportStatusReady : Prop
  exportToR7Ready : Prop
  gateActive : Prop

/-- R3-specific export-surface readiness.

This intentionally avoids the shared short dot-name `ExportSurface.ready` under
the theorem-surface namespaces. -/
def r3_export_surface_ready (S : ExportSurface) : Prop :=
  S.shiftedReady ∧ S.kernelRouteReady ∧ S.exportStatusReady ∧ S.exportToR7Ready ∧ S.gateActive

theorem r3_export_surface_pack
    (S : ExportSurface) :
    r3_export_surface_ready S ↔
      S.shiftedReady ∧ S.kernelRouteReady ∧ S.exportStatusReady ∧ S.exportToR7Ready ∧ S.gateActive := by
  rfl

structure R3TheoremSurface where
  shifted : ShiftedSurface
  kernelRoute : KernelRouteSurface
  exportSurface : ExportSurface

def R3TheoremSurface.ready (S : R3TheoremSurface) : Prop :=
  S.shifted.ready ∧ S.kernelRoute.ready ∧ r3_export_surface_ready S.exportSurface

theorem r3_theorem_surface_pack
    (S : R3TheoremSurface) :
    S.ready ↔ S.shifted.ready ∧ S.kernelRoute.ready ∧ r3_export_surface_ready S.exportSurface := by
  rfl

end TheoremSurface
end R3
end MGAP4D
