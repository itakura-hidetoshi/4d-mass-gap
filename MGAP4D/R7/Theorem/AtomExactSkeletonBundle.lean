import MGAP4D.R7.Concrete.AtomExactCandidateBundle
import MGAP4D.R7.Theorem.AtomExactSkeleton

namespace MGAP4D
namespace R7
namespace Theorem

structure AtomExactSkeletonBundle where
  concreteCandidateReady : Prop
  theoremSkeletonReady : Prop
  mathlibStillDeferred : Prop
  statusCompatibilityHeld : Prop
  publicBoundaryHeld : Prop

def AtomExactSkeletonBundle.ready (B : AtomExactSkeletonBundle) : Prop :=
  B.concreteCandidateReady ∧ B.theoremSkeletonReady ∧ B.mathlibStillDeferred ∧
  B.statusCompatibilityHeld ∧ B.publicBoundaryHeld

theorem atom_exact_skeleton_bundle_pack
    (B : AtomExactSkeletonBundle) :
    B.ready ↔ B.concreteCandidateReady ∧ B.theoremSkeletonReady ∧ B.mathlibStillDeferred ∧
      B.statusCompatibilityHeld ∧ B.publicBoundaryHeld := by
  rfl

end Theorem
end R7
end MGAP4D
