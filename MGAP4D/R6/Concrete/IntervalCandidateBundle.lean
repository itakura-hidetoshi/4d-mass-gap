import MGAP4D.R6.Concrete.IntervalTheoremCandidate
import MGAP4D.ReplacementPass2.R5R6R7RouteBundle

namespace MGAP4D
namespace R6
namespace Concrete

structure IntervalCandidateBundle where
  candidateReady : Prop
  r5r6r7RoutePass2Ready : Prop
  statusPreserved : Prop
  mathlibStillDeferred : Prop
  publicBoundaryHeld : Prop

def IntervalCandidateBundle.ready (B : IntervalCandidateBundle) : Prop :=
  B.candidateReady ∧ B.r5r6r7RoutePass2Ready ∧ B.statusPreserved ∧
  B.mathlibStillDeferred ∧ B.publicBoundaryHeld

theorem interval_candidate_bundle_pack
    (B : IntervalCandidateBundle) :
    B.ready ↔ B.candidateReady ∧ B.r5r6r7RoutePass2Ready ∧ B.statusPreserved ∧
      B.mathlibStillDeferred ∧ B.publicBoundaryHeld := by
  rfl

end Concrete
end R6
end MGAP4D
