import MGAP4D.R2.Concrete.SpectrumUnionStatus

namespace MGAP4D
namespace R2
namespace Concrete

structure ExportStatus where
  reducingSubspaceReady : Prop
  selfAdjointRestrictionReady : Prop
  excitedHamiltonianReady : Prop
  spectrumUnionReady : Prop
  exportToR3Ready : Prop
  exportToR4Ready : Prop
  exportToR5Ready : Prop

def ExportStatus.ready (S : ExportStatus) : Prop :=
  S.reducingSubspaceReady ∧ S.selfAdjointRestrictionReady ∧
  S.excitedHamiltonianReady ∧ S.spectrumUnionReady ∧
  S.exportToR3Ready ∧ S.exportToR4Ready ∧ S.exportToR5Ready

theorem export_status_pack
    (S : ExportStatus) :
    S.ready ↔ S.reducingSubspaceReady ∧ S.selfAdjointRestrictionReady ∧
      S.excitedHamiltonianReady ∧ S.spectrumUnionReady ∧
      S.exportToR3Ready ∧ S.exportToR4Ready ∧ S.exportToR5Ready := by
  rfl

end Concrete
end R2
end MGAP4D
