import MGAP4D.R6.Concrete.GapIntervalStatus
import MGAP4D.MathlibAdoptionGate.R6IntervalRequest

namespace MGAP4D
namespace R6
namespace Concrete

structure IntervalTheoremCandidate where
  gapIntervalStatusReady : Prop
  r5CandidateReady : Prop
  vacuumSideCandidate : Prop
  excitedSideCandidate : Prop
  intervalExclusionCandidate : Prop
  r6IntervalRequestReady : Prop
  mathlibStillDeferred : Prop

def IntervalTheoremCandidate.ready (C : IntervalTheoremCandidate) : Prop :=
  C.gapIntervalStatusReady ∧ C.r5CandidateReady ∧ C.vacuumSideCandidate ∧
  C.excitedSideCandidate ∧ C.intervalExclusionCandidate ∧
  C.r6IntervalRequestReady ∧ C.mathlibStillDeferred

theorem interval_theorem_candidate_pack
    (C : IntervalTheoremCandidate) :
    C.ready ↔ C.gapIntervalStatusReady ∧ C.r5CandidateReady ∧ C.vacuumSideCandidate ∧
      C.excitedSideCandidate ∧ C.intervalExclusionCandidate ∧
      C.r6IntervalRequestReady ∧ C.mathlibStillDeferred := by
  rfl

end Concrete
end R6
end MGAP4D
