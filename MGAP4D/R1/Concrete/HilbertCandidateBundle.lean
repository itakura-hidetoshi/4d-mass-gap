import MGAP4D.R1.Concrete.HilbertTheoremCandidate
import MGAP4D.R1.Concrete.Pass2Bundle

namespace MGAP4D
namespace R1
namespace Concrete

structure R1HilbertCandidateBundle where
  hilbertCandidateReady : Prop
  r1ClosurePass2Ready : Prop
  statusPreserved : Prop
  mathlibStillDeferred : Prop
  publicBoundaryHeld : Prop

def R1HilbertCandidateBundle.ready (B : R1HilbertCandidateBundle) : Prop :=
  B.hilbertCandidateReady ∧ B.r1ClosurePass2Ready ∧ B.statusPreserved ∧
  B.mathlibStillDeferred ∧ B.publicBoundaryHeld

theorem r1_hilbert_candidate_bundle_pack
    (B : R1HilbertCandidateBundle) :
    B.ready ↔ B.hilbertCandidateReady ∧ B.r1ClosurePass2Ready ∧ B.statusPreserved ∧
      B.mathlibStillDeferred ∧ B.publicBoundaryHeld := by
  rfl

end Concrete
end R1
end MGAP4D
