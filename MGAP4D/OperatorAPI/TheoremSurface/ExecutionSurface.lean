import MGAP4D.OperatorAPI.ClosureWorkUnitExecutionStatus
import MGAP4D.OperatorAPI.TheoremSurface.DependencySurface

namespace MGAP4D
namespace OperatorAPI
namespace TheoremSurface

structure ExecutionSurface where
  dependencySurfaceReady : Prop
  r1ExecutableSurface : Prop
  r2ExecutableSurface : Prop
  r4ExecutableSurface : Prop
  r3ExecutableSurface : Prop
  r7ExecutableSurface : Prop
  globalAuditSurface : Prop

def ExecutionSurface.ready (S : ExecutionSurface) : Prop :=
  S.dependencySurfaceReady ∧ S.r1ExecutableSurface ∧ S.r2ExecutableSurface ∧
  S.r4ExecutableSurface ∧ S.r3ExecutableSurface ∧ S.r7ExecutableSurface ∧
  S.globalAuditSurface

theorem execution_surface_pack
    (S : ExecutionSurface) :
    S.ready ↔ S.dependencySurfaceReady ∧ S.r1ExecutableSurface ∧ S.r2ExecutableSurface ∧
      S.r4ExecutableSurface ∧ S.r3ExecutableSurface ∧ S.r7ExecutableSurface ∧
      S.globalAuditSurface := by
  rfl

structure ExecutionGateSurface where
  ciGate : Prop
  auditGate : Prop
  dependencyGate : Prop
  reviewGate : Prop

def ExecutionGateSurface.ready (S : ExecutionGateSurface) : Prop :=
  S.ciGate ∧ S.auditGate ∧ S.dependencyGate ∧ S.reviewGate

theorem execution_gate_surface_pack
    (S : ExecutionGateSurface) :
    S.ready ↔ S.ciGate ∧ S.auditGate ∧ S.dependencyGate ∧ S.reviewGate := by
  rfl

end TheoremSurface
end OperatorAPI
end MGAP4D
