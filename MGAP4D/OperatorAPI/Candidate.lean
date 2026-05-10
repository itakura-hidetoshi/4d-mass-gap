namespace MGAP4D
namespace OperatorAPI

structure CandidateAPI where
  name : String
  layer : String
  purpose : String
  active : Bool
  deriving Repr, DecidableEq

def candidateRegistry : List CandidateAPI := [
  { name := "R1-ELL-CLM", layer := "R1", purpose := "inner functional and closed-kernel route", active := true },
  { name := "R1-PROJECTION", layer := "R1", purpose := "vacuum/excited projection export", active := true },
  { name := "R2-REDUCING-SPECTRUM", layer := "R2", purpose := "reducing decomposition and spectrum union", active := true },
  { name := "R4-LOWER-BOUND", layer := "R4", purpose := "operator lower bound route", active := true },
  { name := "R3-UNBOUNDED-KERNEL", layer := "R3", purpose := "shifted nonnegative kernel route", active := true },
  { name := "R7-ATOM-EXACT-GAP", layer := "R7", purpose := "atom persistence and exact gap", active := true }
]

theorem candidateRegistry_nonempty : candidateRegistry.length > 0 := by
  decide

end OperatorAPI
end MGAP4D
