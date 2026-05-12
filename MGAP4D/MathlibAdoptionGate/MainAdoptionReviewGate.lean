import MGAP4D.MathlibAdoptionGate.DryRunSeriesReviewR1R7

namespace MGAP4D
namespace MathlibAdoptionGate

structure MainAdoptionReviewGate where
  dryRunSeriesReviewed : Prop
  dryRunSuccessNotMainPermission : Prop
  lakefileScopeReviewed : Prop
  manifestBehaviorReviewed : Prop
  importGroupMinimalityReviewed : Prop
  theoremRoutesReviewed : Prop
  publicBoundaryReviewed : Prop
  rollbackPlanReviewed : Prop
  finalAdoptionBranchCIGreen : Prop
  explicitAdoptionDecisionRecorded : Prop
  mainPreMathlibUntilDecision : Prop

def MainAdoptionReviewGate.ready (G : MainAdoptionReviewGate) : Prop :=
  G.dryRunSeriesReviewed ∧ G.dryRunSuccessNotMainPermission ∧
  G.lakefileScopeReviewed ∧ G.manifestBehaviorReviewed ∧
  G.importGroupMinimalityReviewed ∧ G.theoremRoutesReviewed ∧
  G.publicBoundaryReviewed ∧ G.rollbackPlanReviewed ∧
  G.finalAdoptionBranchCIGreen ∧ G.explicitAdoptionDecisionRecorded ∧
  G.mainPreMathlibUntilDecision

theorem main_adoption_review_gate_pack (G : MainAdoptionReviewGate) :
    G.ready ↔ G.dryRunSeriesReviewed ∧ G.dryRunSuccessNotMainPermission ∧
      G.lakefileScopeReviewed ∧ G.manifestBehaviorReviewed ∧
      G.importGroupMinimalityReviewed ∧ G.theoremRoutesReviewed ∧
      G.publicBoundaryReviewed ∧ G.rollbackPlanReviewed ∧
      G.finalAdoptionBranchCIGreen ∧ G.explicitAdoptionDecisionRecorded ∧
      G.mainPreMathlibUntilDecision := by
  rfl

end MathlibAdoptionGate
end MGAP4D
