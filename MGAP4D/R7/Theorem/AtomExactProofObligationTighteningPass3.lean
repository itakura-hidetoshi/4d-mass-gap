import MGAP4D.R7.Theorem.AtomExactProofObligationTighteningPass2

namespace MGAP4D
namespace R7
namespace Theorem

structure AtomExactProofObligationTighteningPass3 where
  pass2Visible : Prop
  upstreamR6ReviewDependencySurfaceVisible : Prop
  finalAssemblyReviewGateSurfaceVisible : Prop
  upstreamR6ReviewGated : Prop
  finalAssemblyReviewGated : Prop
  r7CompletionNotInferredFromUpstreamVisibility : Prop
  finalGapReleaseNotInferredFromR7Visibility : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  theoremCompletionNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def AtomExactProofObligationTighteningPass3.ready
    (P : AtomExactProofObligationTighteningPass3) : Prop :=
  P.pass2Visible ∧ P.upstreamR6ReviewDependencySurfaceVisible ∧
  P.finalAssemblyReviewGateSurfaceVisible ∧ P.upstreamR6ReviewGated ∧
  P.finalAssemblyReviewGated ∧ P.r7CompletionNotInferredFromUpstreamVisibility ∧
  P.finalGapReleaseNotInferredFromR7Visibility ∧ P.mainPreMathlib ∧
  P.mathlibMainAdoptionHeld ∧ P.theoremCompletionNotClaimed ∧
  P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld

theorem atom_exact_proof_obligation_tightening_pass3_pack
    (P : AtomExactProofObligationTighteningPass3) :
    P.ready ↔ P.pass2Visible ∧ P.upstreamR6ReviewDependencySurfaceVisible ∧
      P.finalAssemblyReviewGateSurfaceVisible ∧ P.upstreamR6ReviewGated ∧
      P.finalAssemblyReviewGated ∧ P.r7CompletionNotInferredFromUpstreamVisibility ∧
      P.finalGapReleaseNotInferredFromR7Visibility ∧ P.mainPreMathlib ∧
      P.mathlibMainAdoptionHeld ∧ P.theoremCompletionNotClaimed ∧
      P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld := by
  rfl

end Theorem
end R7
end MGAP4D
