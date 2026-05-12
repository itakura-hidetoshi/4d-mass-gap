import MGAP4D.R5.Theorem.SpectrumMilestone
import MGAP4D.R5.Theorem.SpectrumSkeletonBundle

namespace MGAP4D
namespace R5
namespace Theorem

structure SpectrumInfimumClosureCandidate where
  milestonePresent : Prop
  skeletonBundlePresent : Prop
  spectrumSurfaceNamed : Prop
  infimumBridgeNamed : Prop
  spectrumInfimumObligationsVisible : Prop
  upstreamR4LowerBoundVisible : Prop
  downstreamR6R7ReviewGated : Prop
  mathlibDryRunNotCompletion : Prop
  publicBoundaryHeld : Prop

def SpectrumInfimumClosureCandidate.ready (C : SpectrumInfimumClosureCandidate) : Prop :=
  C.milestonePresent ∧ C.skeletonBundlePresent ∧ C.spectrumSurfaceNamed ∧
  C.infimumBridgeNamed ∧ C.spectrumInfimumObligationsVisible ∧
  C.upstreamR4LowerBoundVisible ∧ C.downstreamR6R7ReviewGated ∧
  C.mathlibDryRunNotCompletion ∧ C.publicBoundaryHeld

theorem spectrum_infimum_closure_candidate_pack (C : SpectrumInfimumClosureCandidate) :
    C.ready ↔ C.milestonePresent ∧ C.skeletonBundlePresent ∧ C.spectrumSurfaceNamed ∧
      C.infimumBridgeNamed ∧ C.spectrumInfimumObligationsVisible ∧
      C.upstreamR4LowerBoundVisible ∧ C.downstreamR6R7ReviewGated ∧
      C.mathlibDryRunNotCompletion ∧ C.publicBoundaryHeld := by
  rfl

end Theorem
end R5
end MGAP4D
