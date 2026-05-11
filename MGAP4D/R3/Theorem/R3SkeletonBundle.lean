import MGAP4D.R3.Concrete.R3CandidateBundle
import MGAP4D.R3.Theorem.R3Skeleton

namespace MGAP4D
namespace R3
namespace Theorem

structure R3SkeletonBundle where
  concreteCandidateReady : Prop
  theoremSkeletonReady : Prop
  mathlibStillDeferred : Prop
  statusCompatibilityHeld : Prop
  publicBoundaryHeld : Prop

def R3SkeletonBundle.ready (B : R3SkeletonBundle) : Prop :=
  B.concreteCandidateReady ∧ B.theoremSkeletonReady ∧ B.mathlibStillDeferred ∧
  B.statusCompatibilityHeld ∧ B.publicBoundaryHeld

theorem r3_skeleton_bundle_pack
    (B : R3SkeletonBundle) :
    B.ready ↔ B.concreteCandidateReady ∧ B.theoremSkeletonReady ∧ B.mathlibStillDeferred ∧
      B.statusCompatibilityHeld ∧ B.publicBoundaryHeld := by
  rfl

end Theorem
end R3
end MGAP4D
