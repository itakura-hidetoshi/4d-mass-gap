import MGAP4D.R1.Concrete.ProjectionStatus

namespace MGAP4D
namespace R1
namespace Concrete

structure ClosureTargetsStatus where
  ellCLMTargetRecorded : Prop
  kernelIffTargetRecorded : Prop
  closedKernelTargetRecorded : Prop
  vacuumLineClosedTargetRecorded : Prop
  orthogonalDecompositionTargetRecorded : Prop
  projectionPairTargetRecorded : Prop
  exportTargetRecorded : Prop

def ClosureTargetsStatus.ready (S : ClosureTargetsStatus) : Prop :=
  S.ellCLMTargetRecorded ∧ S.kernelIffTargetRecorded ∧ S.closedKernelTargetRecorded ∧
  S.vacuumLineClosedTargetRecorded ∧ S.orthogonalDecompositionTargetRecorded ∧
  S.projectionPairTargetRecorded ∧ S.exportTargetRecorded

theorem closure_targets_status_pack
    (S : ClosureTargetsStatus) :
    S.ready ↔ S.ellCLMTargetRecorded ∧ S.kernelIffTargetRecorded ∧ S.closedKernelTargetRecorded ∧
      S.vacuumLineClosedTargetRecorded ∧ S.orthogonalDecompositionTargetRecorded ∧
      S.projectionPairTargetRecorded ∧ S.exportTargetRecorded := by
  rfl

end Concrete
end R1
end MGAP4D
