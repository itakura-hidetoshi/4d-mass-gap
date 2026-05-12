import MGAP4D.R4.Theorem.LowerBoundProofObligationTighteningPass2

namespace MGAP4D
namespace R4
namespace Theorem

structure LowerBoundProofObligationTighteningPass3 where
  pass2Visible : Prop
  upstreamR3ReviewDependencySurfaceVisible : Prop
  upstreamR2BridgeDependencySurfaceVisible : Prop
  downstreamR5R7ReviewGateSurfaceVisible : Prop
  upstreamR3ReviewGated : Prop
  upstreamR2BridgeReviewGated : Prop
  downstreamR5R7ReviewGated : Prop
  r4CompletionNotInferredFromUpstreamVisibility : Prop
  downstreamCompletionNotInferredFromR4Visibility : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  theoremCompletionNotClaimed : Prop
  downstreamR5R7NotUnlocked : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def LowerBoundProofObligationTighteningPass3.ready
    (P : LowerBoundProofObligationTighteningPass3) : Prop :=
  P.pass2Visible ∧ P.upstreamR3ReviewDependencySurfaceVisible ∧
  P.upstreamR2BridgeDependencySurfaceVisible ∧ P.downstreamR5R7ReviewGateSurfaceVisible ∧
  P.upstreamR3ReviewGated ∧ P.upstreamR2BridgeReviewGated ∧
  P.downstreamR5R7ReviewGated ∧ P.r4CompletionNotInferredFromUpstreamVisibility ∧
  P.downstreamCompletionNotInferredFromR4Visibility ∧ P.mainPreMathlib ∧
  P.mathlibMainAdoptionHeld ∧ P.theoremCompletionNotClaimed ∧
  P.downstreamR5R7NotUnlocked ∧ P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld

theorem lower_bound_proof_obligation_tightening_pass3_pack
    (P : LowerBoundProofObligationTighteningPass3) :
    P.ready ↔ P.pass2Visible ∧ P.upstreamR3ReviewDependencySurfaceVisible ∧
      P.upstreamR2BridgeDependencySurfaceVisible ∧ P.downstreamR5R7ReviewGateSurfaceVisible ∧
      P.upstreamR3ReviewGated ∧ P.upstreamR2BridgeReviewGated ∧
      P.downstreamR5R7ReviewGated ∧ P.r4CompletionNotInferredFromUpstreamVisibility ∧
      P.downstreamCompletionNotInferredFromR4Visibility ∧ P.mainPreMathlib ∧
      P.mathlibMainAdoptionHeld ∧ P.theoremCompletionNotClaimed ∧
      P.downstreamR5R7NotUnlocked ∧ P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld := by
  rfl

end Theorem
end R4
end MGAP4D
