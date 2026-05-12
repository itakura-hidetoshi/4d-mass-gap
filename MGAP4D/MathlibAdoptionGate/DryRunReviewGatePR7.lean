import MGAP4D.MathlibAdoptionGate.DryRunResultLedger
import MGAP4D.R6.Theorem.IntervalMilestone

namespace MGAP4D
namespace MathlibAdoptionGate

structure DryRunReviewGatePR7 where
  prNumberRecorded : Prop
  ci603SuccessRecorded : Prop
  r6IntervalDryRunBuildable : Prop
  intervalExclusionRouteStillDeferred : Prop
  lakefileScopeRequiresReview : Prop
  importGroupRequiresReview : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop
  mergeNotAutomatic : Prop
  mainRemainsPreMathlibUntilDecision : Prop

def DryRunReviewGatePR7.ready (G : DryRunReviewGatePR7) : Prop :=
  G.prNumberRecorded ∧ G.ci603SuccessRecorded ∧ G.r6IntervalDryRunBuildable ∧
  G.intervalExclusionRouteStillDeferred ∧ G.lakefileScopeRequiresReview ∧
  G.importGroupRequiresReview ∧ G.statusSurfacesPreserved ∧ G.publicBoundaryHeld ∧
  G.mergeNotAutomatic ∧ G.mainRemainsPreMathlibUntilDecision

theorem dry_run_review_gate_pr7_pack (G : DryRunReviewGatePR7) :
    G.ready ↔ G.prNumberRecorded ∧ G.ci603SuccessRecorded ∧ G.r6IntervalDryRunBuildable ∧
      G.intervalExclusionRouteStillDeferred ∧ G.lakefileScopeRequiresReview ∧
      G.importGroupRequiresReview ∧ G.statusSurfacesPreserved ∧ G.publicBoundaryHeld ∧
      G.mergeNotAutomatic ∧ G.mainRemainsPreMathlibUntilDecision := by
  rfl

end MathlibAdoptionGate
end MGAP4D
