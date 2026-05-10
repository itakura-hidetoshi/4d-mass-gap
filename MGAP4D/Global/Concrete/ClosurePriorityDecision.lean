namespace MGAP4D
namespace Global
namespace Concrete

inductive ClosurePriorityDecision where
  | proceed
  | hold
  | defer
  deriving Repr, DecidableEq

structure ClosurePriorityDecisionRecord where
  decision : ClosurePriorityDecision
  reason : String
  gate_active : Prop
  deriving Repr

def defaultClosurePriorityDecision : ClosurePriorityDecisionRecord :=
  { decision := ClosurePriorityDecision.proceed,
    reason := "status-only closure priority batch",
    gate_active := True }

theorem default_closure_priority_gate : defaultClosurePriorityDecision.gate_active := by
  trivial

end Concrete
end Global
end MGAP4D
