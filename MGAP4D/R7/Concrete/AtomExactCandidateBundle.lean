import MGAP4D.R7.Concrete.AtomExactTheoremCandidate
import MGAP4D.ReplacementPass2.R5R6R7RouteBundle

namespace MGAP4D
namespace R7
namespace Concrete

structure AtomExactCandidateBundle where
  candidateReady : Prop
  r5r6r7RoutePass2Ready : Prop
  statusPreserved : Prop
  mathlibStillDeferred : Prop
  publicBoundaryHeld : Prop

def AtomExactCandidateBundle.ready (B : AtomExactCandidateBundle) : Prop :=
  B.candidateReady ∧ B.r5r6r7RoutePass2Ready ∧ B.statusPreserved ∧
  B.mathlibStillDeferred ∧ B.publicBoundaryHeld

theorem atom_exact_candidate_bundle_pack
    (B : AtomExactCandidateBundle) :
    B.ready ↔ B.candidateReady ∧ B.r5r6r7RoutePass2Ready ∧ B.statusPreserved ∧
      B.mathlibStillDeferred ∧ B.publicBoundaryHeld := by
  rfl

end Concrete
end R7
end MGAP4D
