import MGAP4D.OperatorAPI.AdoptionPlan

namespace MGAP4D
namespace OperatorAPI

inductive PhaseId where
  | phase1
  | phase2
  | phase3
  | terminal
  deriving Repr, DecidableEq

structure PhasePlanEntry where
  phase : PhaseId
  name : String
  active : Bool
  deriving Repr, DecidableEq

def phasePlan : List PhasePlanEntry := [
  { phase := PhaseId.phase1, name := "R1/R2/R5 interface setup", active := true },
  { phase := PhaseId.phase2, name := "R3 unbounded kernel route", active := true },
  { phase := PhaseId.phase3, name := "R4/R7 exact gap route", active := true },
  { phase := PhaseId.terminal, name := "global final audit", active := true }
]

theorem phasePlan_nonempty : phasePlan.length > 0 := by
  decide

end OperatorAPI
end MGAP4D
