import MGAP4D.R6.Theorem.IntervalExclusionProofObligationTighteningPass2

namespace MGAP4D
namespace R6
namespace Theorem

structure IntervalExclusionProofObligationTighteningPass3 where
  pass2Visible : Prop
  upstreamR5ReviewDependencySurfaceVisible : Prop
  downstreamR7ReviewGateSurfaceVisible : Prop
  upstreamR5ReviewGated : Prop
  downstreamR7ReviewGated : Prop
  r6CompletionNotInferredFromUpstreamVisibility : Prop
  downstreamCompletionNotInferredFromR6Visibility : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  theoremCompletionNotClaimed : Prop
  downstreamR7NotUnlocked : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def IntervalExclusionProofObligationTighteningPass3.ready
    (P : IntervalExclusionProofObligationTighteningPass3) : Prop :=
  P.pass2Visible ∧ P.upstreamR5ReviewDependencySurfaceVisible ∧
  P.downstreamR7ReviewGateSurfaceVisible ∧ P.upstreamR5ReviewGated ∧
  P.downstreamR7ReviewGated ∧ P.r6CompletionNotInferredFromUpstreamVisibility ∧
  P.downstreamCompletionNotInferredFromR6Visibility ∧ P.mainPreMathlib ∧
  P.mathlibMainAdoptionHeld ∧ P.theoremCompletionNotClaimed ∧
  P.downstreamR7NotUnlocked ∧ P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld

theorem interval_exclusion_proof_obligation_tightening_pass3_pack
    (P : IntervalExclusionProofObligationTighteningPass3) :
    P.ready ↔ P.pass2Visible ∧ P.upstreamR5ReviewDependencySurfaceVisible ∧
      P.downstreamR7ReviewGateSurfaceVisible ∧ P.upstreamR5ReviewGated ∧
      P.downstreamR7ReviewGated ∧ P.r6CompletionNotInferredFromUpstreamVisibility ∧
      P.downstreamCompletionNotInferredFromR6Visibility ∧ P.mainPreMathlib ∧
      P.mathlibMainAdoptionHeld ∧ P.theoremCompletionNotClaimed ∧
      P.downstreamR7NotUnlocked ∧ P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld := by
  rfl

end Theorem
end R6
end MGAP4D
