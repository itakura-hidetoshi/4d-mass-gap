import MGAP4D.R2.Theorem.RestrictionProofObligationTighteningSeriesReview

namespace MGAP4D
namespace R2
namespace Theorem

structure RestrictionProofObligationTighteningClosure where
  pass1Green : Prop
  pass2Green : Prop
  pass3Green : Prop
  seriesReviewGreen : Prop
  tighteningSequenceClosedAtReviewSurface : Prop
  reducingSubspaceClosedAtReviewSurface : Prop
  fullHamiltonianSelfAdjointClosedAtReviewSurface : Prop
  restrictionDomainClosedAtReviewSurface : Prop
  restrictionOperatorClosedAtReviewSurface : Prop
  restrictionSelfAdjointClosedAtReviewSurface : Prop
  operatorAPIBridgeClosedAtReviewSurface : Prop
  mathlibRequestBoundaryClosedAtReviewSurface : Prop
  statusCompatibilityBoundaryClosedAtReviewSurface : Prop
  publicBoundaryClosedAtReviewSurface : Prop
  r1ClosurePreservationClosedAtReviewSurface : Prop
  finalReleaseNonInferenceClosedAtReviewSurface : Prop
  threeLayerLinksClosedAtReviewSurface : Prop
  r2TheoremRouteStillOpen : Prop
  r1ClosurePreserved : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  r2TheoremCompletionNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def RestrictionProofObligationTighteningClosure.ready
    (C : RestrictionProofObligationTighteningClosure) : Prop :=
  C.pass1Green ∧ C.pass2Green ∧ C.pass3Green ∧ C.seriesReviewGreen ∧
  C.tighteningSequenceClosedAtReviewSurface ∧ C.reducingSubspaceClosedAtReviewSurface ∧
  C.fullHamiltonianSelfAdjointClosedAtReviewSurface ∧ C.restrictionDomainClosedAtReviewSurface ∧
  C.restrictionOperatorClosedAtReviewSurface ∧ C.restrictionSelfAdjointClosedAtReviewSurface ∧
  C.operatorAPIBridgeClosedAtReviewSurface ∧ C.mathlibRequestBoundaryClosedAtReviewSurface ∧
  C.statusCompatibilityBoundaryClosedAtReviewSurface ∧ C.publicBoundaryClosedAtReviewSurface ∧
  C.r1ClosurePreservationClosedAtReviewSurface ∧ C.finalReleaseNonInferenceClosedAtReviewSurface ∧
  C.threeLayerLinksClosedAtReviewSurface ∧ C.r2TheoremRouteStillOpen ∧
  C.r1ClosurePreserved ∧ C.mainPreMathlib ∧ C.mathlibMainAdoptionHeld ∧
  C.r2TheoremCompletionNotClaimed ∧ C.finalGapReleaseNotUnlocked ∧ C.publicBoundaryHeld

theorem restriction_proof_obligation_tightening_closure_pack
    (C : RestrictionProofObligationTighteningClosure) :
    C.ready ↔ C.pass1Green ∧ C.pass2Green ∧ C.pass3Green ∧ C.seriesReviewGreen ∧
      C.tighteningSequenceClosedAtReviewSurface ∧ C.reducingSubspaceClosedAtReviewSurface ∧
      C.fullHamiltonianSelfAdjointClosedAtReviewSurface ∧ C.restrictionDomainClosedAtReviewSurface ∧
      C.restrictionOperatorClosedAtReviewSurface ∧ C.restrictionSelfAdjointClosedAtReviewSurface ∧
      C.operatorAPIBridgeClosedAtReviewSurface ∧ C.mathlibRequestBoundaryClosedAtReviewSurface ∧
      C.statusCompatibilityBoundaryClosedAtReviewSurface ∧ C.publicBoundaryClosedAtReviewSurface ∧
      C.r1ClosurePreservationClosedAtReviewSurface ∧ C.finalReleaseNonInferenceClosedAtReviewSurface ∧
      C.threeLayerLinksClosedAtReviewSurface ∧ C.r2TheoremRouteStillOpen ∧
      C.r1ClosurePreserved ∧ C.mainPreMathlib ∧ C.mathlibMainAdoptionHeld ∧
      C.r2TheoremCompletionNotClaimed ∧ C.finalGapReleaseNotUnlocked ∧ C.publicBoundaryHeld := by
  rfl

end Theorem
end R2
end MGAP4D
