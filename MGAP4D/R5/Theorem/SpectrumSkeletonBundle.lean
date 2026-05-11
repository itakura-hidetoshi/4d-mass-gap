import MGAP4D.R5.Concrete.SpectrumCandidateBundle
import MGAP4D.R5.Theorem.SpectrumSkeleton

namespace MGAP4D
namespace R5
namespace Theorem

structure SpectrumSkeletonBundle where
  concreteCandidateReady : Prop
  theoremSkeletonReady : Prop
  mathlibStillDeferred : Prop
  statusCompatibilityHeld : Prop
  publicBoundaryHeld : Prop

def SpectrumSkeletonBundle.ready (B : SpectrumSkeletonBundle) : Prop :=
  B.concreteCandidateReady ∧ B.theoremSkeletonReady ∧ B.mathlibStillDeferred ∧
  B.statusCompatibilityHeld ∧ B.publicBoundaryHeld

theorem spectrum_skeleton_bundle_pack
    (B : SpectrumSkeletonBundle) :
    B.ready ↔ B.concreteCandidateReady ∧ B.theoremSkeletonReady ∧ B.mathlibStillDeferred ∧
      B.statusCompatibilityHeld ∧ B.publicBoundaryHeld := by
  rfl

end Theorem
end R5
end MGAP4D
