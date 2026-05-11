import MGAP4D.R3.Concrete.R3TheoremCandidate
import MGAP4D.ReplacementPass2.R2R4R3RouteBundle

namespace MGAP4D
namespace R3
namespace Concrete

structure R3CandidateBundle where
  candidateReady : Prop
  r2r4r3RoutePass2Ready : Prop
  statusPreserved : Prop
  mathlibStillDeferred : Prop
  publicBoundaryHeld : Prop

def R3CandidateBundle.ready (B : R3CandidateBundle) : Prop :=
  B.candidateReady ∧ B.r2r4r3RoutePass2Ready ∧ B.statusPreserved ∧
  B.mathlibStillDeferred ∧ B.publicBoundaryHeld

theorem r3_candidate_bundle_pack
    (B : R3CandidateBundle) :
    B.ready ↔ B.candidateReady ∧ B.r2r4r3RoutePass2Ready ∧ B.statusPreserved ∧
      B.mathlibStillDeferred ∧ B.publicBoundaryHeld := by
  rfl

end Concrete
end R3
end MGAP4D
