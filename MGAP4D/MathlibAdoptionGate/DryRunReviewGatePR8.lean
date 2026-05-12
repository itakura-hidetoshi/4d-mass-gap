import MGAP4D.MathlibAdoptionGate.DryRunResultLedger
import MGAP4D.R7.Theorem.AtomExactMilestone

namespace MGAP4D
namespace MathlibAdoptionGate

structure DryRunReviewGatePR8 where
  prNumberRecorded : Prop
  ci612SuccessRecorded : Prop
  r7AtomExactDryRunBuildable : Prop
  atomExactGapRouteStillDeferred : Prop
  lakefileScopeRequiresReview : Prop
  importGroupRequiresReview : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop
  mergeNotAutomatic : Prop
  mainRemainsPreMathlibUntilDecision : Prop

def DryRunReviewGatePR8.ready (G : DryRunReviewGatePR8) : Prop :=
  G.prNumberRecorded ∧ G.ci612SuccessRecorded ∧ G.r7AtomExactDryRunBuildable ∧
  G.atomExactGapRouteStillDeferred ∧ G.lakefileScopeRequiresReview ∧
  G.importGroupRequiresReview ∧ G.statusSurfacesPreserved ∧ G.publicBoundaryHeld ∧
  G.mergeNotAutomatic ∧ G.mainRemainsPreMathlibUntilDecision

theorem dry_run_review_gate_pr8_pack (G : DryRunReviewGatePR8) :
    G.ready ↔ G.prNumberRecorded ∧ G.ci612SuccessRecorded ∧ G.r7AtomExactDryRunBuildable ∧
      G.atomExactGapRouteStillDeferred ∧ G.lakefileScopeRequiresReview ∧
      G.importGroupRequiresReview ∧ G.statusSurfacesPreserved ∧ G.publicBoundaryHeld ∧
      G.mergeNotAutomatic ∧ G.mainRemainsPreMathlibUntilDecision := by
  rfl

end MathlibAdoptionGate
end MGAP4D
