import MGAP4D.R5.Concrete.SpectrumSetStatus

namespace MGAP4D
namespace R5
namespace Concrete

structure InfimumStatus where
  spectrumSetReady : Prop
  bottomRecorded : Prop
  membershipRecorded : Prop
  comparisonSurfaceRecorded : Prop
  proofBindingDeferred : Prop

def InfimumStatus.ready (S : InfimumStatus) : Prop :=
  S.spectrumSetReady ∧ S.bottomRecorded ∧ S.membershipRecorded ∧ S.comparisonSurfaceRecorded ∧ S.proofBindingDeferred

theorem infimum_status_pack
    (S : InfimumStatus) :
    S.ready ↔ S.spectrumSetReady ∧ S.bottomRecorded ∧ S.membershipRecorded ∧ S.comparisonSurfaceRecorded ∧ S.proofBindingDeferred := by
  rfl

end Concrete
end R5
end MGAP4D
