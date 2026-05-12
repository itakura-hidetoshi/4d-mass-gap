import MGAP4D.R4.Theorem.LowerBoundMilestone
import MGAP4D.R4.Theorem.LowerBoundSkeletonBundle

namespace MGAP4D
namespace R4
namespace Theorem

structure LowerBoundClosureCandidate where
  milestonePresent : Prop
  skeletonBundlePresent : Prop
  lowerBoundRouteNamed : Prop
  lowerBoundObligationsVisible : Prop
  upstreamDependencyVisible : Prop
  downstreamR5R7ReviewGated : Prop
  mathlibDryRunNotCompletion : Prop
  publicBoundaryHeld : Prop

def LowerBoundClosureCandidate.ready (C : LowerBoundClosureCandidate) : Prop :=
  C.milestonePresent ∧ C.skeletonBundlePresent ∧ C.lowerBoundRouteNamed ∧
  C.lowerBoundObligationsVisible ∧ C.upstreamDependencyVisible ∧
  C.downstreamR5R7ReviewGated ∧ C.mathlibDryRunNotCompletion ∧ C.publicBoundaryHeld

theorem lower_bound_closure_candidate_pack (C : LowerBoundClosureCandidate) :
    C.ready ↔ C.milestonePresent ∧ C.skeletonBundlePresent ∧ C.lowerBoundRouteNamed ∧
      C.lowerBoundObligationsVisible ∧ C.upstreamDependencyVisible ∧
      C.downstreamR5R7ReviewGated ∧ C.mathlibDryRunNotCompletion ∧ C.publicBoundaryHeld := by
  rfl

end Theorem
end R4
end MGAP4D
