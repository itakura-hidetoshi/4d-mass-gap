import MGAP4D.R6.Theorem.IntervalMilestone
import MGAP4D.R6.Theorem.IntervalSkeletonBundle

namespace MGAP4D
namespace R6
namespace Theorem

structure IntervalExclusionClosureCandidate where
  milestonePresent : Prop
  skeletonBundlePresent : Prop
  intervalSurfaceNamed : Prop
  exclusionBoundaryNamed : Prop
  intervalExclusionObligationsVisible : Prop
  upstreamR5SpectrumInfimumVisible : Prop
  downstreamR7AtomExactReviewGated : Prop
  mathlibDryRunNotCompletion : Prop
  publicBoundaryHeld : Prop

def IntervalExclusionClosureCandidate.ready (C : IntervalExclusionClosureCandidate) : Prop :=
  C.milestonePresent ∧ C.skeletonBundlePresent ∧ C.intervalSurfaceNamed ∧
  C.exclusionBoundaryNamed ∧ C.intervalExclusionObligationsVisible ∧
  C.upstreamR5SpectrumInfimumVisible ∧ C.downstreamR7AtomExactReviewGated ∧
  C.mathlibDryRunNotCompletion ∧ C.publicBoundaryHeld

theorem interval_exclusion_closure_candidate_pack (C : IntervalExclusionClosureCandidate) :
    C.ready ↔ C.milestonePresent ∧ C.skeletonBundlePresent ∧ C.intervalSurfaceNamed ∧
      C.exclusionBoundaryNamed ∧ C.intervalExclusionObligationsVisible ∧
      C.upstreamR5SpectrumInfimumVisible ∧ C.downstreamR7AtomExactReviewGated ∧
      C.mathlibDryRunNotCompletion ∧ C.publicBoundaryHeld := by
  rfl

end Theorem
end R6
end MGAP4D
