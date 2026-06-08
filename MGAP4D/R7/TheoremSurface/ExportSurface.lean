import MGAP4D.R7.TheoremSurface.ExactGapSurface

namespace MGAP4D
namespace R7
namespace TheoremSurface

structure ExportSurface where
  atomReady : Prop
  exactReady : Prop
  globalReady : Prop
  gateActive : Prop

/-- R7-specific export-surface readiness.

This intentionally avoids the short dot-name `ExportSurface.ready`, because the
preflight short-name audit treats that declaration as shared across the R1--R7
surface files. -/
def r7_export_surface_ready (S : ExportSurface) : Prop :=
  S.atomReady ∧ S.exactReady ∧ S.globalReady ∧ S.gateActive

theorem r7_export_surface_pack
    (S : ExportSurface) :
    r7_export_surface_ready S ↔ S.atomReady ∧ S.exactReady ∧ S.globalReady ∧ S.gateActive := by
  rfl

structure R7TheoremSurface where
  atom : AtomSurface
  exactGap : ExactGapSurface
  exportSurface : ExportSurface

def R7TheoremSurface.ready (S : R7TheoremSurface) : Prop :=
  S.atom.ready ∧ S.exactGap.ready ∧ r7_export_surface_ready S.exportSurface

theorem r7_theorem_surface_pack
    (S : R7TheoremSurface) :
    S.ready ↔ S.atom.ready ∧ S.exactGap.ready ∧ r7_export_surface_ready S.exportSurface := by
  rfl

end TheoremSurface
end R7
end MGAP4D
