import MGAP4D.R6.Theorem.IntervalExclusionClosureCandidate

namespace MGAP4D
namespace R6
namespace Theorem

structure IntervalExclusionHardeningPass where
  closureCandidateVisible : Prop
  intervalSurfaceVisible : Prop
  exclusionBoundaryVisible : Prop
  intervalExclusionObligationsVisible : Prop
  upstreamR5SpectrumInfimumVisible : Prop
  downstreamR7AtomExactReviewGated : Prop
  mathlibDryRunNotCompletion : Prop
  theoremCompletionNotClaimed : Prop
  publicBoundaryHeld : Prop

def IntervalExclusionHardeningPass.ready (P : IntervalExclusionHardeningPass) : Prop :=
  P.closureCandidateVisible ∧ P.intervalSurfaceVisible ∧
  P.exclusionBoundaryVisible ∧ P.intervalExclusionObligationsVisible ∧
  P.upstreamR5SpectrumInfimumVisible ∧ P.downstreamR7AtomExactReviewGated ∧
  P.mathlibDryRunNotCompletion ∧ P.theoremCompletionNotClaimed ∧ P.publicBoundaryHeld

theorem interval_exclusion_hardening_pass_pack (P : IntervalExclusionHardeningPass) :
    P.ready ↔ P.closureCandidateVisible ∧ P.intervalSurfaceVisible ∧
      P.exclusionBoundaryVisible ∧ P.intervalExclusionObligationsVisible ∧
      P.upstreamR5SpectrumInfimumVisible ∧ P.downstreamR7AtomExactReviewGated ∧
      P.mathlibDryRunNotCompletion ∧ P.theoremCompletionNotClaimed ∧ P.publicBoundaryHeld := by
  rfl

end Theorem
end R6
end MGAP4D
