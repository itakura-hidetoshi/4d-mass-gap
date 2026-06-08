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

def ExportSurface.ready (S : ExportSurface) : Prop :=
  S.intervalReady ∧ S.exportStatusReady ∧ S.globalReady ∧ S.gateActive

theorem export_surface_pack
    (S : ExportSurface) :
    S.ready ↔ S.intervalReady ∧ S.exportStatusReady ∧ S.globalReady ∧ S.gateActive := by
  rfl

structure R6TheoremSurface where
  interval : GapIntervalSurface
  exportSurface : ExportSurface

def R6TheoremSurface.ready (S : R6TheoremSurface) : Prop :=
  S.interval.ready ∧ S.exportSurface.ready

theorem r6_theorem_surface_pack
    (S : R6TheoremSurface) :
    S.ready ↔ S.interval.ready ∧ S.exportSurface.ready := by
  rfl

end TheoremSurface
end R6
end MGAP4D
