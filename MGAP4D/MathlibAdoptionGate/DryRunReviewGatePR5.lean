import MGAP4D.MathlibAdoptionGate.DryRunResultLedger
import MGAP4D.R4.Theorem.LowerBoundMilestone

namespace MGAP4D
namespace MathlibAdoptionGate

structure DryRunReviewGatePR5 where
  prNumberRecorded : Prop
  ci584SuccessRecorded : Prop
  r4LowerBoundDryRunBuildable : Prop
  lowerBoundRouteStillDeferred : Prop
  lakefileScopeRequiresReview : Prop
  importGroupRequiresReview : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop
  mergeNotAutomatic : Prop
  mainRemainsPreMathlibUntilDecision : Prop

def DryRunReviewGatePR5.ready (G : DryRunReviewGatePR5) : Prop :=
  G.prNumberRecorded ∧ G.ci584SuccessRecorded ∧ G.r4LowerBoundDryRunBuildable ∧
  G.lowerBoundRouteStillDeferred ∧ G.lakefileScopeRequiresReview ∧
  G.importGroupRequiresReview ∧ G.statusSurfacesPreserved ∧ G.publicBoundaryHeld ∧
  G.mergeNotAutomatic ∧ G.mainRemainsPreMathlibUntilDecision

theorem dry_run_review_gate_pr5_pack (G : DryRunReviewGatePR5) :
    G.ready ↔ G.prNumberRecorded ∧ G.ci584SuccessRecorded ∧ G.r4LowerBoundDryRunBuildable ∧
      G.lowerBoundRouteStillDeferred ∧ G.lakefileScopeRequiresReview ∧
      G.importGroupRequiresReview ∧ G.statusSurfacesPreserved ∧ G.publicBoundaryHeld ∧
      G.mergeNotAutomatic ∧ G.mainRemainsPreMathlibUntilDecision := by
  rfl

end MathlibAdoptionGate
end MGAP4D
