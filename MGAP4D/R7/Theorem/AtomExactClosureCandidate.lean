import MGAP4D.R7.Theorem.AtomExactMilestone
import MGAP4D.R7.Theorem.AtomExactSkeletonBundle

namespace MGAP4D
namespace R7
namespace Theorem

structure AtomExactClosureCandidate where
  milestonePresent : Prop
  skeletonBundlePresent : Prop
  atomSurfaceNamed : Prop
  exactGapSurfaceNamed : Prop
  finalValueBoundaryReviewGated : Prop
  atomExactObligationsVisible : Prop
  upstreamR5SpectrumInfimumVisible : Prop
  upstreamR6IntervalExclusionVisible : Prop
  mathlibDryRunNotCompletion : Prop
  publicBoundaryHeld : Prop

def AtomExactClosureCandidate.ready (C : AtomExactClosureCandidate) : Prop :=
  C.milestonePresent ∧ C.skeletonBundlePresent ∧ C.atomSurfaceNamed ∧
  C.exactGapSurfaceNamed ∧ C.finalValueBoundaryReviewGated ∧
  C.atomExactObligationsVisible ∧ C.upstreamR5SpectrumInfimumVisible ∧
  C.upstreamR6IntervalExclusionVisible ∧ C.mathlibDryRunNotCompletion ∧ C.publicBoundaryHeld

theorem atom_exact_closure_candidate_pack (C : AtomExactClosureCandidate) :
    C.ready ↔ C.milestonePresent ∧ C.skeletonBundlePresent ∧ C.atomSurfaceNamed ∧
      C.exactGapSurfaceNamed ∧ C.finalValueBoundaryReviewGated ∧
      C.atomExactObligationsVisible ∧ C.upstreamR5SpectrumInfimumVisible ∧
      C.upstreamR6IntervalExclusionVisible ∧ C.mathlibDryRunNotCompletion ∧ C.publicBoundaryHeld := by
  rfl

end Theorem
end R7
end MGAP4D
