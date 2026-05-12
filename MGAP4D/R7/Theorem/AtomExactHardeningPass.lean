import MGAP4D.R7.Theorem.AtomExactClosureCandidate

namespace MGAP4D
namespace R7
namespace Theorem

structure AtomExactHardeningPass where
  closureCandidateVisible : Prop
  atomSurfaceVisible : Prop
  exactGapSurfaceVisible : Prop
  finalValueBoundaryReviewGated : Prop
  atomExactObligationsVisible : Prop
  upstreamR5SpectrumInfimumVisible : Prop
  upstreamR6IntervalExclusionVisible : Prop
  mathlibDryRunNotCompletion : Prop
  theoremCompletionNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def AtomExactHardeningPass.ready (P : AtomExactHardeningPass) : Prop :=
  P.closureCandidateVisible ∧ P.atomSurfaceVisible ∧
  P.exactGapSurfaceVisible ∧ P.finalValueBoundaryReviewGated ∧
  P.atomExactObligationsVisible ∧ P.upstreamR5SpectrumInfimumVisible ∧
  P.upstreamR6IntervalExclusionVisible ∧ P.mathlibDryRunNotCompletion ∧
  P.theoremCompletionNotClaimed ∧ P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld

theorem atom_exact_hardening_pass_pack (P : AtomExactHardeningPass) :
    P.ready ↔ P.closureCandidateVisible ∧ P.atomSurfaceVisible ∧
      P.exactGapSurfaceVisible ∧ P.finalValueBoundaryReviewGated ∧
      P.atomExactObligationsVisible ∧ P.upstreamR5SpectrumInfimumVisible ∧
      P.upstreamR6IntervalExclusionVisible ∧ P.mathlibDryRunNotCompletion ∧
      P.theoremCompletionNotClaimed ∧ P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld := by
  rfl

end Theorem
end R7
end MGAP4D
