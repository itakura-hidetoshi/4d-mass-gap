import MGAP4D.R2.Concrete.RestrictionTheoremCandidate
import MGAP4D.ReplacementPass2.R2R4R3RouteBundle

namespace MGAP4D
namespace R2
namespace Concrete

structure R2RestrictionCandidateBundle where
  restrictionCandidateReady : Prop
  r2r4r3RoutePass2Ready : Prop
  statusPreserved : Prop
  mathlibStillDeferred : Prop
  publicBoundaryHeld : Prop

def R2RestrictionCandidateBundle.ready (B : R2RestrictionCandidateBundle) : Prop :=
  B.restrictionCandidateReady ∧ B.r2r4r3RoutePass2Ready ∧ B.statusPreserved ∧
  B.mathlibStillDeferred ∧ B.publicBoundaryHeld

theorem r2_restriction_candidate_bundle_pack
    (B : R2RestrictionCandidateBundle) :
    B.ready ↔ B.restrictionCandidateReady ∧ B.r2r4r3RoutePass2Ready ∧ B.statusPreserved ∧
      B.mathlibStillDeferred ∧ B.publicBoundaryHeld := by
  rfl

end Concrete
end R2
end MGAP4D
