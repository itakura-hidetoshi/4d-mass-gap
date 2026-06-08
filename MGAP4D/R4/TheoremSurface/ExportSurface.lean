import MGAP4D.R4.TheoremSurface.BridgeSurface

namespace MGAP4D
namespace R4
namespace TheoremSurface

structure ExportSurface where
  lbReady : Prop
  bridgeReady : Prop
  r3Ready : Prop
  r5Ready : Prop
  gateActive : Prop

/-- R4-specific export-surface readiness.

This intentionally avoids the shared short dot-name `ExportSurface.ready` under
the theorem-surface namespaces. -/
def r4_export_surface_ready (S : ExportSurface) : Prop :=
  S.lbReady ∧ S.bridgeReady ∧ S.r3Ready ∧ S.r5Ready ∧ S.gateActive

theorem r4_export_surface_pack
    (S : ExportSurface) :
    r4_export_surface_ready S ↔ S.lbReady ∧ S.bridgeReady ∧ S.r3Ready ∧ S.r5Ready ∧ S.gateActive := by
  rfl

structure R4TheoremSurface where
  lowerBound : LowerBoundSurface
  bridge : BridgeSurface
  exportSurface : ExportSurface

def R4TheoremSurface.ready (S : R4TheoremSurface) : Prop :=
  S.lowerBound.ready ∧ S.bridge.ready ∧ r4_export_surface_ready S.exportSurface

theorem r4_theorem_surface_pack
    (S : R4TheoremSurface) :
    S.ready ↔ S.lowerBound.ready ∧ S.bridge.ready ∧ r4_export_surface_ready S.exportSurface := by
  rfl

end TheoremSurface
end R4
end MGAP4D
