import MGAP4D.R5.Theorem.SpectrumInfimumClosureCandidate

namespace MGAP4D
namespace R5
namespace Theorem

structure SpectrumInfimumHardeningPass where
  closureCandidateVisible : Prop
  spectrumSurfaceVisible : Prop
  infimumBridgeVisible : Prop
  spectrumInfimumObligationsVisible : Prop
  upstreamR4LowerBoundVisible : Prop
  downstreamR6R7ReviewGated : Prop
  mathlibDryRunNotCompletion : Prop
  theoremCompletionNotClaimed : Prop
  publicBoundaryHeld : Prop

def SpectrumInfimumHardeningPass.ready (P : SpectrumInfimumHardeningPass) : Prop :=
  P.closureCandidateVisible ∧ P.spectrumSurfaceVisible ∧
  P.infimumBridgeVisible ∧ P.spectrumInfimumObligationsVisible ∧
  P.upstreamR4LowerBoundVisible ∧ P.downstreamR6R7ReviewGated ∧
  P.mathlibDryRunNotCompletion ∧ P.theoremCompletionNotClaimed ∧ P.publicBoundaryHeld

theorem spectrum_infimum_hardening_pass_pack (P : SpectrumInfimumHardeningPass) :
    P.ready ↔ P.closureCandidateVisible ∧ P.spectrumSurfaceVisible ∧
      P.infimumBridgeVisible ∧ P.spectrumInfimumObligationsVisible ∧
      P.upstreamR4LowerBoundVisible ∧ P.downstreamR6R7ReviewGated ∧
      P.mathlibDryRunNotCompletion ∧ P.theoremCompletionNotClaimed ∧ P.publicBoundaryHeld := by
  rfl

end Theorem
end R5
end MGAP4D
