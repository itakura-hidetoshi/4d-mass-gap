import MGAP4D.MathlibAdoptionGate.DryRunResultLedger

namespace MGAP4D
namespace MathlibAdoptionGate

structure DryRunReviewGatePR1 where
  prNumberRecorded : Prop
  ci381SuccessRecorded : Prop
  ci382SuccessRecorded : Prop
  r1HilbertDryRunBuildable : Prop
  lakefileScopeRequiresReview : Prop
  importGroupRequiresReview : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop
  mergeNotAutomatic : Prop
  mainRemainsPreMathlibUntilDecision : Prop

def DryRunReviewGatePR1.ready (G : DryRunReviewGatePR1) : Prop :=
  G.prNumberRecorded ∧ G.ci381SuccessRecorded ∧ G.ci382SuccessRecorded ∧
  G.r1HilbertDryRunBuildable ∧ G.lakefileScopeRequiresReview ∧
  G.importGroupRequiresReview ∧ G.statusSurfacesPreserved ∧ G.publicBoundaryHeld ∧
  G.mergeNotAutomatic ∧ G.mainRemainsPreMathlibUntilDecision

theorem dry_run_review_gate_pr1_pack
    (G : DryRunReviewGatePR1) :
    G.ready ↔ G.prNumberRecorded ∧ G.ci381SuccessRecorded ∧ G.ci382SuccessRecorded ∧
      G.r1HilbertDryRunBuildable ∧ G.lakefileScopeRequiresReview ∧
      G.importGroupRequiresReview ∧ G.statusSurfacesPreserved ∧ G.publicBoundaryHeld ∧
      G.mergeNotAutomatic ∧ G.mainRemainsPreMathlibUntilDecision := by
  rfl

end MathlibAdoptionGate
end MGAP4D
