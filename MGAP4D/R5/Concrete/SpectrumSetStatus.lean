import MGAP4D.R4.Concrete

namespace MGAP4D
namespace R5
namespace Concrete

structure SpectrumSetStatus where
  r4Ready : Prop
  excitedSpectrumRecorded : Prop
  totalSpectrumRecorded : Prop
  lowerSurfaceRecorded : Prop
  bindingDeferred : Prop

def SpectrumSetStatus.ready (S : SpectrumSetStatus) : Prop :=
  S.r4Ready ∧ S.excitedSpectrumRecorded ∧ S.totalSpectrumRecorded ∧ S.lowerSurfaceRecorded ∧ S.bindingDeferred

theorem spectrum_set_status_pack
    (S : SpectrumSetStatus) :
    S.ready ↔ S.r4Ready ∧ S.excitedSpectrumRecorded ∧ S.totalSpectrumRecorded ∧ S.lowerSurfaceRecorded ∧ S.bindingDeferred := by
  rfl

end Concrete
end R5
end MGAP4D
