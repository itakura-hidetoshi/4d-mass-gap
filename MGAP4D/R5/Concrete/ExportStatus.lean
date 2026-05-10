import MGAP4D.R5.Concrete.InfimumStatus

namespace MGAP4D
namespace R5
namespace Concrete

structure ExportStatus where
  spectrumReady : Prop
  bottomReady : Prop
  exportToR6Ready : Prop
  exportToGlobalReady : Prop
  reviewGateActive : Prop

def ExportStatus.ready (S : ExportStatus) : Prop :=
  S.spectrumReady ∧ S.bottomReady ∧ S.exportToR6Ready ∧ S.exportToGlobalReady ∧ S.reviewGateActive

theorem export_status_pack
    (S : ExportStatus) :
    S.ready ↔ S.spectrumReady ∧ S.bottomReady ∧ S.exportToR6Ready ∧ S.exportToGlobalReady ∧ S.reviewGateActive := by
  rfl

end Concrete
end R5
end MGAP4D
