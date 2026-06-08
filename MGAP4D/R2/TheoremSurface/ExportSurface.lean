import MGAP4D.R2.TheoremSurface.SpectrumSurface
import MGAP4D.R2.Concrete.ExportStatus

namespace MGAP4D
namespace R2
namespace TheoremSurface

structure ExportSurface where
  spectrumSurfaceReady : Prop
  exportStatusReady : Prop
  exportToR3Surface : Prop
  exportToR4Surface : Prop
  exportToR5Surface : Prop
  reviewGateActive : Prop

/-- R2-specific export-surface readiness.

This intentionally avoids the shared short dot-name `ExportSurface.ready` under
the theorem-surface namespaces. -/
def r2_export_surface_ready (S : ExportSurface) : Prop :=
  S.spectrumSurfaceReady ∧ S.exportStatusReady ∧ S.exportToR3Surface ∧
  S.exportToR4Surface ∧ S.exportToR5Surface ∧ S.reviewGateActive

theorem r2_export_surface_pack
    (S : ExportSurface) :
    r2_export_surface_ready S ↔ S.spectrumSurfaceReady ∧ S.exportStatusReady ∧ S.exportToR3Surface ∧
      S.exportToR4Surface ∧ S.exportToR5Surface ∧ S.reviewGateActive := by
  rfl

structure R2TheoremSurface where
  reducing : ReducingSurface
  restriction : RestrictionSurface
  excitedHamiltonian : ExcitedHamiltonianSurface
  spectrum : SpectrumSurface
  exportSurface : ExportSurface

def R2TheoremSurface.ready (S : R2TheoremSurface) : Prop :=
  S.reducing.ready ∧ S.restriction.ready ∧ S.excitedHamiltonian.ready ∧
  S.spectrum.ready ∧ r2_export_surface_ready S.exportSurface

theorem r2_theorem_surface_pack
    (S : R2TheoremSurface) :
    S.ready ↔ S.reducing.ready ∧ S.restriction.ready ∧ S.excitedHamiltonian.ready ∧
      S.spectrum.ready ∧ r2_export_surface_ready S.exportSurface := by
  rfl

end TheoremSurface
end R2
end MGAP4D
