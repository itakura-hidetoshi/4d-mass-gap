import MGAP4D.R4.Concrete.LowerBoundCandidateBundle
import MGAP4D.R4.Theorem.LowerBoundSkeleton

namespace MGAP4D
namespace R4
namespace Theorem

structure LowerBoundSkeletonBundle where
  concreteCandidateReady : Prop
  theoremSkeletonReady : Prop
  mathlibStillDeferred : Prop
  statusCompatibilityHeld : Prop
  publicBoundaryHeld : Prop

def LowerBoundSkeletonBundle.ready (B : LowerBoundSkeletonBundle) : Prop :=
  B.concreteCandidateReady ∧ B.theoremSkeletonReady ∧ B.mathlibStillDeferred ∧
  B.statusCompatibilityHeld ∧ B.publicBoundaryHeld

theorem lower_bound_skeleton_bundle_pack
    (B : LowerBoundSkeletonBundle) :
    B.ready ↔ B.concreteCandidateReady ∧ B.theoremSkeletonReady ∧ B.mathlibStillDeferred ∧
      B.statusCompatibilityHeld ∧ B.publicBoundaryHeld := by
  rfl

end Theorem
end R4
end MGAP4D
