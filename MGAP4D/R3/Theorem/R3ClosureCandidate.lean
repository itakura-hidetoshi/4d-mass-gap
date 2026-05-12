import MGAP4D.R3.Theorem.R3Milestone
import MGAP4D.R3.Theorem.R3SkeletonBundle

namespace MGAP4D
namespace R3
namespace Theorem

structure R3ClosureCandidate where
  milestonePresent : Prop
  skeletonBundlePresent : Prop
  shiftedRouteNamed : Prop
  zeroFormRouteNamed : Prop
  operatorBoundaryVisible : Prop
  proofObligationsVisible : Prop
  downstreamR4R7ReviewGated : Prop
  mathlibDryRunNotCompletion : Prop
  publicBoundaryHeld : Prop

def R3ClosureCandidate.ready (C : R3ClosureCandidate) : Prop :=
  C.milestonePresent ∧ C.skeletonBundlePresent ∧ C.shiftedRouteNamed ∧
  C.zeroFormRouteNamed ∧ C.operatorBoundaryVisible ∧ C.proofObligationsVisible ∧
  C.downstreamR4R7ReviewGated ∧ C.mathlibDryRunNotCompletion ∧ C.publicBoundaryHeld

theorem r3_closure_candidate_pack (C : R3ClosureCandidate) :
    C.ready ↔ C.milestonePresent ∧ C.skeletonBundlePresent ∧ C.shiftedRouteNamed ∧
      C.zeroFormRouteNamed ∧ C.operatorBoundaryVisible ∧ C.proofObligationsVisible ∧
      C.downstreamR4R7ReviewGated ∧ C.mathlibDryRunNotCompletion ∧ C.publicBoundaryHeld := by
  rfl

end Theorem
end R3
end MGAP4D
