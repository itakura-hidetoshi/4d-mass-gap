namespace MGAP4D
namespace Migration

inductive MathlibDecision where
  | deferred
  | adoptWhenNeeded
  | adopted
  deriving Repr, DecidableEq

structure MathlibPolicyStatus where
  decision : MathlibDecision
  reason : String
  ciRequired : Bool
  deriving Repr, DecidableEq

def currentMathlibPolicy : MathlibPolicyStatus :=
  { decision := MathlibDecision.deferred,
    reason := "minimal Lean project until theorem-level concrete modules require Mathlib",
    ciRequired := true }

theorem currentMathlibPolicy_ciRequired : currentMathlibPolicy.ciRequired = true := by
  rfl

end Migration
end MGAP4D
