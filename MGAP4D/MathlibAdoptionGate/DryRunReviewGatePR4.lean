import MGAP4D.MathlibAdoptionGate.DryRunResultLedger
import MGAP4D.R3.Theorem.R3Milestone

namespace MGAP4D
namespace MathlibAdoptionGate

structure DryRunReviewGatePR4 where
  prNumberRecorded : Prop
  ci576SuccessRecorded : Prop
  r3ZeroFormDryRunBuildable : Prop
  zeroFormRouteStillDeferred : Prop
  lakefileScopeRequiresReview : Prop
  importGroupRequiresReview : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop
  mergeNotAutomatic : Prop
  mainRemainsPreMathlibUntilDecision : Prop

def DryRunReviewGatePR4.ready (G : DryRunReviewGatePR4) : Prop :=
  G.prNumberRecorded ∧ G.ci576SuccessRecorded ∧ G.r3ZeroFormDryRunBuildable ∧
  G.zeroFormRouteStillDeferred ∧ G.lakefileScopeRequiresReview ∧
  G.importGroupRequiresReview ∧ G.statusSurfacesPreserved ∧ G.publicBoundaryHeld ∧
  G.mergeNotAutomatic ∧ G.mainRemainsPreMathlibUntilDecision

theorem dry_run_review_gate_pr4_pack (G : DryRunReviewGatePR4) :
    G.ready ↔ G.prNumberRecorded ∧ G.ci576SuccessRecorded ∧ G.r3ZeroFormDryRunBuildable ∧
      G.zeroFormRouteStillDeferred ∧ G.lakefileScopeRequiresReview ∧
      G.importGroupRequiresReview ∧ G.statusSurfacesPreserved ∧ G.publicBoundaryHeld ∧
      G.mergeNotAutomatic ∧ G.mainRemainsPreMathlibUntilDecision := by
  rfl

end MathlibAdoptionGate
end MGAP4D
