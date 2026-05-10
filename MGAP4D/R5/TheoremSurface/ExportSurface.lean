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

def ExportSurface.ready (S : ExportSurface) : Prop :=
  S.spectrumReady ∧ S.bottomReady ∧ S.exportStatusReady ∧
  S.r6Ready ∧ S.globalReady ∧ S.gateActive

theorem export_surface_pack
    (S : ExportSurface) :
    S.ready ↔ S.spectrumReady ∧ S.bottomReady ∧ S.exportStatusReady ∧
      S.r6Ready ∧ S.globalReady ∧ S.gateActive := by
  rfl

structure R5TheoremSurface where
  spectrumSet : SpectrumSetSurface
  infimum : InfimumSurface
  export : ExportSurface

def R5TheoremSurface.ready (S : R5TheoremSurface) : Prop :=
  S.spectrumSet.ready ∧ S.infimum.ready ∧ S.export.ready

theorem r5_theorem_surface_pack
    (S : R5TheoremSurface) :
    S.ready ↔ S.spectrumSet.ready ∧ S.infimum.ready ∧ S.export.ready := by
  rfl

end TheoremSurface
end R5
end MGAP4D
