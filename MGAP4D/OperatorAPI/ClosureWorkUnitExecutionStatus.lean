import MGAP4D.OperatorAPI.PhaseSelectionStatus

namespace MGAP4D
namespace OperatorAPI

structure ClosureWorkUnitExecutionStatus where
  r1EllCLMReady : Prop
  r1ProjectionReady : Prop
  r2ReducingSpectrumReady : Prop
  r4LowerBoundReady : Prop
  r3UnboundedKernelReady : Prop
  r7AtomExactGapReady : Prop
  globalFinalAuditReady : Prop

def ClosureWorkUnitExecutionStatus.ready (S : ClosureWorkUnitExecutionStatus) : Prop :=
  S.r1EllCLMReady ∧ S.r1ProjectionReady ∧ S.r2ReducingSpectrumReady ∧
  S.r4LowerBoundReady ∧ S.r3UnboundedKernelReady ∧ S.r7AtomExactGapReady ∧
  S.globalFinalAuditReady

theorem closure_work_unit_execution_status_pack
    (S : ClosureWorkUnitExecutionStatus) :
    S.ready ↔ S.r1EllCLMReady ∧ S.r1ProjectionReady ∧ S.r2ReducingSpectrumReady ∧
      S.r4LowerBoundReady ∧ S.r3UnboundedKernelReady ∧ S.r7AtomExactGapReady ∧
      S.globalFinalAuditReady := by
  rfl

end OperatorAPI
end MGAP4D
