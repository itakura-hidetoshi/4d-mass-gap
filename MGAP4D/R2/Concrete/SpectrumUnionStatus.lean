import MGAP4D.R2.Concrete.ExcitedHamiltonianStatus

namespace MGAP4D
namespace R2
namespace Concrete

structure SpectrumUnionStatus where
  excitedHamiltonianReady : Prop
  vacuumSpectrumTargetRecorded : Prop
  excitedSpectrumTargetRecorded : Prop
  directSumSpectrumTargetRecorded : Prop
  exportToR5Deferred : Prop

def SpectrumUnionStatus.ready (S : SpectrumUnionStatus) : Prop :=
  S.excitedHamiltonianReady ∧ S.vacuumSpectrumTargetRecorded ∧
  S.excitedSpectrumTargetRecorded ∧ S.directSumSpectrumTargetRecorded ∧
  S.exportToR5Deferred

theorem spectrum_union_status_pack
    (S : SpectrumUnionStatus) :
    S.ready ↔ S.excitedHamiltonianReady ∧ S.vacuumSpectrumTargetRecorded ∧
      S.excitedSpectrumTargetRecorded ∧ S.directSumSpectrumTargetRecorded ∧
      S.exportToR5Deferred := by
  rfl

end Concrete
end R2
end MGAP4D
