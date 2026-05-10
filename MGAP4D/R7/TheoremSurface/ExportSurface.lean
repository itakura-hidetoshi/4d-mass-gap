import MGAP4D.R7.TheoremSurface.ExactGapSurface

namespace MGAP4D
namespace R7
namespace TheoremSurface

structure ExportSurface where
  atomReady : Prop
  exactReady : Prop
  globalReady : Prop
  gateActive : Prop

def ExportSurface.ready (S : ExportSurface) : Prop :=
  S.atomReady ∧ S.exactReady ∧ S.globalReady ∧ S.gateActive

theorem export_surface_pack
    (S : ExportSurface) :
    S.ready ↔ S.atomReady ∧ S.exactReady ∧ S.globalReady ∧ S.gateActive := by
  rfl

structure R7TheoremSurface where
  atom : AtomSurface
  exactGap : ExactGapSurface
  export : ExportSurface

def R7TheoremSurface.ready (S : R7TheoremSurface) : Prop :=
  S.atom.ready ∧ S.exactGap.ready ∧ S.export.ready

theorem r7_theorem_surface_pack
    (S : R7TheoremSurface) :
    S.ready ↔ S.atom.ready ∧ S.exactGap.ready ∧ S.export.ready := by
  rfl

end TheoremSurface
end R7
end MGAP4D
