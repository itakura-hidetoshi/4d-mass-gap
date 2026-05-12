import MGAP4D.MathlibAdoptionGate.DryRunResultLedger
import MGAP4D.MathlibAdoptionGate.NextDryRunSelection

namespace MGAP4D
namespace MathlibAdoptionGate

structure DryRunReviewGatePR3 where
  prNumberRecorded : Prop
  ci564SuccessRecorded : Prop
  r2RestrictionDryRunBuildable : Prop
  lakefileScopeRequiresReview : Prop
  importGroupRequiresReview : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop
  mergeNotAutomatic : Prop
  mainRemainsPreMathlibUntilDecision : Prop

def DryRunReviewGatePR3.ready (G : DryRunReviewGatePR3) : Prop :=
  G.prNumberRecorded ∧ G.ci564SuccessRecorded ∧ G.r2RestrictionDryRunBuildable ∧
  G.lakefileScopeRequiresReview ∧ G.importGroupRequiresReview ∧
  G.statusSurfacesPreserved ∧ G.publicBoundaryHeld ∧ G.mergeNotAutomatic ∧
  G.mainRemainsPreMathlibUntilDecision

theorem dry_run_review_gate_pr3_pack
    (G : DryRunReviewGatePR3) :
    G.ready ↔ G.prNumberRecorded ∧ G.ci564SuccessRecorded ∧ G.r2RestrictionDryRunBuildable ∧
      G.lakefileScopeRequiresReview ∧ G.importGroupRequiresReview ∧
      G.statusSurfacesPreserved ∧ G.publicBoundaryHeld ∧ G.mergeNotAutomatic ∧
      G.mainRemainsPreMathlibUntilDecision := by
  rfl

end MathlibAdoptionGate
end MGAP4D
