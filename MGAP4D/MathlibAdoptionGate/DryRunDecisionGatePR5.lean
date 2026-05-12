import MGAP4D.MathlibAdoptionGate.DryRunReviewGatePR5

namespace MGAP4D
namespace MathlibAdoptionGate

inductive PR5DryRunDecision where
  | holdDraft
  | closeAsSuccessfulDryRun
  | prepareReviewedAdoptionProposal
  deriving Repr, DecidableEq

structure PR5CloseAsDryRunGate where
  dryRunSuccessRecorded : Prop
  resultLedgerRecorded : Prop
  mainRemainsPreMathlib : Prop
  prClosedWithoutMerge : Prop
  futureAdoptionRequiresNewProposal : Prop

def PR5CloseAsDryRunGate.ready (G : PR5CloseAsDryRunGate) : Prop :=
  G.dryRunSuccessRecorded ∧ G.resultLedgerRecorded ∧ G.mainRemainsPreMathlib ∧
  G.prClosedWithoutMerge ∧ G.futureAdoptionRequiresNewProposal

theorem pr5_close_as_dry_run_gate_pack (G : PR5CloseAsDryRunGate) :
    G.ready ↔ G.dryRunSuccessRecorded ∧ G.resultLedgerRecorded ∧ G.mainRemainsPreMathlib ∧
      G.prClosedWithoutMerge ∧ G.futureAdoptionRequiresNewProposal := by
  rfl

structure PR5ReviewedAdoptionGate where
  dryRunSuccessRecorded : Prop
  lowerBoundRouteReviewed : Prop
  lakefileScopeReviewed : Prop
  manifestBehaviorReviewed : Prop
  importGroupReviewed : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop
  finalHeadCIGreen : Prop
  stillRequiresExplicitDecision : Prop

def PR5ReviewedAdoptionGate.ready (G : PR5ReviewedAdoptionGate) : Prop :=
  G.dryRunSuccessRecorded ∧ G.lowerBoundRouteReviewed ∧ G.lakefileScopeReviewed ∧
  G.manifestBehaviorReviewed ∧ G.importGroupReviewed ∧ G.statusSurfacesPreserved ∧
  G.publicBoundaryHeld ∧ G.finalHeadCIGreen ∧ G.stillRequiresExplicitDecision

theorem pr5_reviewed_adoption_gate_pack (G : PR5ReviewedAdoptionGate) :
    G.ready ↔ G.dryRunSuccessRecorded ∧ G.lowerBoundRouteReviewed ∧ G.lakefileScopeReviewed ∧
      G.manifestBehaviorReviewed ∧ G.importGroupReviewed ∧ G.statusSurfacesPreserved ∧
      G.publicBoundaryHeld ∧ G.finalHeadCIGreen ∧ G.stillRequiresExplicitDecision := by
  rfl

structure PR5CloseOrAdvanceGate where
  reviewGateReady : Prop
  decisionRecorded : Prop
  decision : PR5DryRunDecision
  noAutomaticMerge : Prop

def PR5CloseOrAdvanceGate.ready (G : PR5CloseOrAdvanceGate) : Prop :=
  G.reviewGateReady ∧ G.decisionRecorded ∧ G.noAutomaticMerge

theorem pr5_close_or_advance_gate_pack (G : PR5CloseOrAdvanceGate) :
    G.ready ↔ G.reviewGateReady ∧ G.decisionRecorded ∧ G.noAutomaticMerge := by
  rfl

end MathlibAdoptionGate
end MGAP4D
