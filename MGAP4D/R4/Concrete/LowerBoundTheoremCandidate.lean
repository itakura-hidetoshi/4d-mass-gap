import MGAP4D.R4.Concrete.LowerBoundReceiptStatus
import MGAP4D.MathlibAdoptionGate.R4LowerBoundRequest

namespace MGAP4D
namespace R4
namespace Concrete

structure LowerBoundTheoremCandidate where
  receiptReady : Prop
  excitedHamiltonianCandidate : Prop
  decompositionLedgerCandidate : Prop
  rationalConstantCandidate : Prop
  theoremTarget : Prop
  r4RequestReady : Prop
  mathlibStillDeferred : Prop

def LowerBoundTheoremCandidate.ready (C : LowerBoundTheoremCandidate) : Prop :=
  C.receiptReady ∧ C.excitedHamiltonianCandidate ∧
  C.decompositionLedgerCandidate ∧ C.rationalConstantCandidate ∧
  C.theoremTarget ∧ C.r4RequestReady ∧ C.mathlibStillDeferred

theorem lower_bound_theorem_candidate_pack
    (C : LowerBoundTheoremCandidate) :
    C.ready ↔ C.receiptReady ∧ C.excitedHamiltonianCandidate ∧
      C.decompositionLedgerCandidate ∧ C.rationalConstantCandidate ∧
      C.theoremTarget ∧ C.r4RequestReady ∧ C.mathlibStillDeferred := by
  rfl

end Concrete
end R4
end MGAP4D
