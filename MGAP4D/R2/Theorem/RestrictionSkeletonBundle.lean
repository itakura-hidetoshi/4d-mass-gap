import MGAP4D.R2.Concrete.RestrictionCandidateBundle
import MGAP4D.R2.Theorem.RestrictionSkeleton

namespace MGAP4D
namespace R2
namespace Theorem

structure RestrictionSkeletonBundle where
  concreteCandidateReady : Prop
  theoremSkeletonReady : Prop
  mathlibStillDeferred : Prop
  statusCompatibilityHeld : Prop
  publicBoundaryHeld : Prop

def RestrictionSkeletonBundle.ready (B : RestrictionSkeletonBundle) : Prop :=
  B.concreteCandidateReady ∧ B.theoremSkeletonReady ∧ B.mathlibStillDeferred ∧
  B.statusCompatibilityHeld ∧ B.publicBoundaryHeld

theorem restriction_skeleton_bundle_pack
    (B : RestrictionSkeletonBundle) :
    B.ready ↔ B.concreteCandidateReady ∧ B.theoremSkeletonReady ∧ B.mathlibStillDeferred ∧
      B.statusCompatibilityHeld ∧ B.publicBoundaryHeld := by
  rfl

end Theorem
end R2
end MGAP4D
