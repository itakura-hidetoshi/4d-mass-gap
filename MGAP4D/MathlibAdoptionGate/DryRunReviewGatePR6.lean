import MGAP4D.MathlibAdoptionGate.DryRunResultLedger
import MGAP4D.R5.Theorem.SpectrumMilestone

namespace MGAP4D
namespace MathlibAdoptionGate

structure DryRunReviewGatePR6 where
  prNumberRecorded : Prop
  ci593SuccessRecorded : Prop
  r5SpectrumDryRunBuildable : Prop
  spectrumInfimumRouteStillDeferred : Prop
  lakefileScopeRequiresReview : Prop
  importGroupRequiresReview : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop
  mergeNotAutomatic : Prop
  mainRemainsPreMathlibUntilDecision : Prop

def DryRunReviewGatePR6.ready (G : DryRunReviewGatePR6) : Prop :=
  G.prNumberRecorded ∧ G.ci593SuccessRecorded ∧ G.r5SpectrumDryRunBuildable ∧
  G.spectrumInfimumRouteStillDeferred ∧ G.lakefileScopeRequiresReview ∧
  G.importGroupRequiresReview ∧ G.statusSurfacesPreserved ∧ G.publicBoundaryHeld ∧
  G.mergeNotAutomatic ∧ G.mainRemainsPreMathlibUntilDecision

theorem dry_run_review_gate_pr6_pack (G : DryRunReviewGatePR6) :
    G.ready ↔ G.prNumberRecorded ∧ G.ci593SuccessRecorded ∧ G.r5SpectrumDryRunBuildable ∧
      G.spectrumInfimumRouteStillDeferred ∧ G.lakefileScopeRequiresReview ∧
      G.importGroupRequiresReview ∧ G.statusSurfacesPreserved ∧ G.publicBoundaryHeld ∧
      G.mergeNotAutomatic ∧ G.mainRemainsPreMathlibUntilDecision := by
  rfl

end MathlibAdoptionGate
end MGAP4D
