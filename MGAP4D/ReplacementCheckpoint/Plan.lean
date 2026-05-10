namespace MGAP4D
namespace ReplacementCheckpoint

inductive ReplacementTarget where
  | operatorAPI
  | r1Closure
  | r2Export
  | r4Export
  | r3Export
  | r5Export
  | r6Export
  | r7Exact
  | globalConcreteSummary
  | finalAssemblyConcrete
  deriving Repr, DecidableEq

structure ReplacementPlanEntry where
  order : Nat
  target : ReplacementTarget
  statusSurfaceKept : Bool
  theoremSurfaceRequired : Bool
  mathlibRequired : Bool
  deriving Repr, DecidableEq

def firstReplacementPlan : List ReplacementPlanEntry := [
  { order := 1, target := ReplacementTarget.operatorAPI, statusSurfaceKept := true, theoremSurfaceRequired := true, mathlibRequired := false },
  { order := 2, target := ReplacementTarget.r1Closure, statusSurfaceKept := true, theoremSurfaceRequired := true, mathlibRequired := false },
  { order := 3, target := ReplacementTarget.r2Export, statusSurfaceKept := true, theoremSurfaceRequired := true, mathlibRequired := false },
  { order := 4, target := ReplacementTarget.r4Export, statusSurfaceKept := true, theoremSurfaceRequired := true, mathlibRequired := false },
  { order := 5, target := ReplacementTarget.r3Export, statusSurfaceKept := true, theoremSurfaceRequired := true, mathlibRequired := false },
  { order := 6, target := ReplacementTarget.r5Export, statusSurfaceKept := true, theoremSurfaceRequired := true, mathlibRequired := false },
  { order := 7, target := ReplacementTarget.r6Export, statusSurfaceKept := true, theoremSurfaceRequired := true, mathlibRequired := false },
  { order := 8, target := ReplacementTarget.r7Exact, statusSurfaceKept := true, theoremSurfaceRequired := true, mathlibRequired := false },
  { order := 9, target := ReplacementTarget.globalConcreteSummary, statusSurfaceKept := true, theoremSurfaceRequired := true, mathlibRequired := false },
  { order := 10, target := ReplacementTarget.finalAssemblyConcrete, statusSurfaceKept := true, theoremSurfaceRequired := true, mathlibRequired := false }
]

theorem firstReplacementPlan_nonempty : firstReplacementPlan.length > 0 := by
  decide

end ReplacementCheckpoint
end MGAP4D
