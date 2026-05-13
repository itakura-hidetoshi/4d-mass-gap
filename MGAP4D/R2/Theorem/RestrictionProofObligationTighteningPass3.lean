import MGAP4D.R2.Theorem.RestrictionProofObligationTighteningPass2

namespace MGAP4D
namespace R2
namespace Theorem

structure RestrictionProofObligationTighteningPass3 where
  pass2Visible : Prop
  mathlibRequestBoundaryReviewSurfaceVisible : Prop
  statusCompatibilityReviewSurfaceVisible : Prop
  publicBoundaryReviewSurfaceVisible : Prop
  r1ClosurePreservationSurfaceVisible : Prop
  finalReleaseNonInferenceSurfaceVisible : Prop
  mathlibRequestReviewGated : Prop
  statusCompatibilityReviewGated : Prop
  publicBoundaryReviewGated : Prop
  r1ClosurePreservationReviewGated : Prop
  r2CompletionNotInferredFromRestrictionVisibility : Prop
  r1ClosureNotReopenedByR2Visibility : Prop
  finalGapReleaseNotInferredFromR2Visibility : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  r2TheoremCompletionNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def RestrictionProofObligationTighteningPass3.ready
    (P : RestrictionProofObligationTighteningPass3) : Prop :=
  P.pass2Visible ∧ P.mathlibRequestBoundaryReviewSurfaceVisible ∧
  P.statusCompatibilityReviewSurfaceVisible ∧ P.publicBoundaryReviewSurfaceVisible ∧
  P.r1ClosurePreservationSurfaceVisible ∧ P.finalReleaseNonInferenceSurfaceVisible ∧
  P.mathlibRequestReviewGated ∧ P.statusCompatibilityReviewGated ∧
  P.publicBoundaryReviewGated ∧ P.r1ClosurePreservationReviewGated ∧
  P.r2CompletionNotInferredFromRestrictionVisibility ∧ P.r1ClosureNotReopenedByR2Visibility ∧
  P.finalGapReleaseNotInferredFromR2Visibility ∧ P.mainPreMathlib ∧
  P.mathlibMainAdoptionHeld ∧ P.r2TheoremCompletionNotClaimed ∧
  P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld

theorem restriction_proof_obligation_tightening_pass3_pack
    (P : RestrictionProofObligationTighteningPass3) :
    P.ready ↔ P.pass2Visible ∧ P.mathlibRequestBoundaryReviewSurfaceVisible ∧
      P.statusCompatibilityReviewSurfaceVisible ∧ P.publicBoundaryReviewSurfaceVisible ∧
      P.r1ClosurePreservationSurfaceVisible ∧ P.finalReleaseNonInferenceSurfaceVisible ∧
      P.mathlibRequestReviewGated ∧ P.statusCompatibilityReviewGated ∧
      P.publicBoundaryReviewGated ∧ P.r1ClosurePreservationReviewGated ∧
      P.r2CompletionNotInferredFromRestrictionVisibility ∧ P.r1ClosureNotReopenedByR2Visibility ∧
      P.finalGapReleaseNotInferredFromR2Visibility ∧ P.mainPreMathlib ∧
      P.mathlibMainAdoptionHeld ∧ P.r2TheoremCompletionNotClaimed ∧
      P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld := by
  rfl

end Theorem
end R2
end MGAP4D
