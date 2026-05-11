import MGAP4D.R4.Concrete.LowerBoundTheoremCandidate
import MGAP4D.ReplacementPass2.R2R4R3RouteBundle

namespace MGAP4D
namespace R4
namespace Concrete

structure LowerBoundCandidateBundle where
  candidateReady : Prop
  r2r4r3RoutePass2Ready : Prop
  statusPreserved : Prop
  mathlibStillDeferred : Prop
  publicBoundaryHeld : Prop

def LowerBoundCandidateBundle.ready (B : LowerBoundCandidateBundle) : Prop :=
  B.candidateReady ∧ B.r2r4r3RoutePass2Ready ∧ B.statusPreserved ∧
  B.mathlibStillDeferred ∧ B.publicBoundaryHeld

theorem lower_bound_candidate_bundle_pack
    (B : LowerBoundCandidateBundle) :
    B.ready ↔ B.candidateReady ∧ B.r2r4r3RoutePass2Ready ∧ B.statusPreserved ∧
      B.mathlibStillDeferred ∧ B.publicBoundaryHeld := by
  rfl

end Concrete
end R4
end MGAP4D
