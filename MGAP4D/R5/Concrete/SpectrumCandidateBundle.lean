import MGAP4D.R5.Concrete.SpectrumTheoremCandidate
import MGAP4D.ReplacementPass2.R5R6R7RouteBundle

namespace MGAP4D
namespace R5
namespace Concrete

structure SpectrumCandidateBundle where
  candidateReady : Prop
  r5r6r7RoutePass2Ready : Prop
  statusPreserved : Prop
  mathlibStillDeferred : Prop
  publicBoundaryHeld : Prop

def SpectrumCandidateBundle.ready (B : SpectrumCandidateBundle) : Prop :=
  B.candidateReady ∧ B.r5r6r7RoutePass2Ready ∧ B.statusPreserved ∧
  B.mathlibStillDeferred ∧ B.publicBoundaryHeld

theorem spectrum_candidate_bundle_pack
    (B : SpectrumCandidateBundle) :
    B.ready ↔ B.candidateReady ∧ B.r5r6r7RoutePass2Ready ∧ B.statusPreserved ∧
      B.mathlibStillDeferred ∧ B.publicBoundaryHeld := by
  rfl

end Concrete
end R5
end MGAP4D
