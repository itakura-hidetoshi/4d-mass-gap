import MGAP4D.R1.TheoremSurface.ProjectionSurface

namespace MGAP4D
namespace R1
namespace TheoremSurface

structure ExportSurface where
  projectionSurfaceReady : Prop
  closureTargetsReady : Prop
  exportToR2Surface : Prop
  reviewGateActive : Prop

/-- R1-specific export-surface readiness.

This intentionally avoids the shared short dot-name `ExportSurface.ready` under
the theorem-surface namespaces. -/
def r1_export_surface_ready (S : ExportSurface) : Prop :=
  S.projectionSurfaceReady ∧ S.closureTargetsReady ∧ S.exportToR2Surface ∧ S.reviewGateActive

theorem r1_export_surface_pack
    (S : ExportSurface) :
    r1_export_surface_ready S ↔
      S.projectionSurfaceReady ∧ S.closureTargetsReady ∧ S.exportToR2Surface ∧ S.reviewGateActive := by
  rfl

structure R1TheoremSurface where
  hilbert : HilbertSurface
  excited : ExcitedSurface
  innerFunctional : InnerFunctionalSurface
  projection : ProjectionSurface
  exportSurface : ExportSurface

def R1TheoremSurface.ready (S : R1TheoremSurface) : Prop :=
  S.hilbert.ready ∧ S.excited.ready ∧ S.innerFunctional.ready ∧
    S.projection.ready ∧ r1_export_surface_ready S.exportSurface

theorem r1_theorem_surface_pack
    (S : R1TheoremSurface) :
    S.ready ↔ S.hilbert.ready ∧ S.excited.ready ∧ S.innerFunctional.ready ∧
      S.projection.ready ∧ r1_export_surface_ready S.exportSurface := by
  rfl

end TheoremSurface
end R1
end MGAP4D
