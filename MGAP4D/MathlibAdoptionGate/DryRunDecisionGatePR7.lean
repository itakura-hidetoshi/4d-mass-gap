import MGAP4D.MathlibAdoptionGate.DryRunReviewGatePR7

namespace MGAP4D
namespace MathlibAdoptionGate

inductive PR7DryRunDecision where
  | holdDraft
  | closeAsSuccessfulDryRun
  | prepareReviewedAdoptionProposal
  deriving Repr, DecidableEq

structure PR7CloseAsDryRunGate where
  dryRunSuccessRecorded : Prop
  resultLedgerRecorded : Prop
  mainRemainsPreMathlib : Prop
  prClosedWithoutMerge : Prop
  futureAdoptionRequiresNewProposal : Prop

def PR7CloseAsDryRunGate.ready (G : PR7CloseAsDryRunGate) : Prop :=
  G.dryRunSuccessRecorded ∧ G.resultLedgerRecorded ∧ G.mainRemainsPreMathlib ∧
  G.prClosedWithoutMerge ∧ G.futureAdoptionRequiresNewProposal

theorem pr7_close_as_dry_run_gate_pack (G : PR7CloseAsDryRunGate) :
    G.ready ↔ G.dryRunSuccessRecorded ∧ G.resultLedgerRecorded ∧ G.mainRemainsPreMathlib ∧
      G.prClosedWithoutMerge ∧ G.futureAdoptionRequiresNewProposal := by
  rfl

structure PR7ReviewedAdoptionGate where
  dryRunSuccessRecorded : Prop
  intervalExclusionRouteReviewed : Prop
  lakefileScopeReviewed : Prop
  manifestBehaviorReviewed : Prop
  importGroupReviewed : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop
  finalHeadCIGreen : Prop
  stillRequiresExplicitDecision : Prop

def PR7ReviewedAdoptionGate.ready (G : PR7ReviewedAdoptionGate) : Prop :=
  G.dryRunSuccessRecorded ∧ G.intervalExclusionRouteReviewed ∧ G.lakefileScopeReviewed ∧
  G.manifestBehaviorReviewed ∧ G.importGroupReviewed ∧ G.statusSurfacesPreserved ∧
  G.publicBoundaryHeld ∧ G.finalHeadCIGreen ∧ G.stillRequiresExplicitDecision

theorem pr7_reviewed_adoption_gate_pack (G : PR7ReviewedAdoptionGate) :
    G.ready ↔ G.dryRunSuccessRecorded ∧ G.intervalExclusionRouteReviewed ∧ G.lakefileScopeReviewed ∧
      G.manifestBehaviorReviewed ∧ G.importGroupReviewed ∧ G.statusSurfacesPreserved ∧
      G.publicBoundaryHeld ∧ G.finalHeadCIGreen ∧ G.stillRequiresExplicitDecision := by
  rfl

structure PR7CloseOrAdvanceGate where
  reviewGateReady : Prop
  decisionRecorded : Prop
  decision : PR7DryRunDecision
  noAutomaticMerge : Prop

def PR7CloseOrAdvanceGate.ready (G : PR7CloseOrAdvanceGate) : Prop :=
  G.reviewGateReady ∧ G.decisionRecorded ∧ G.noAutomaticMerge

theorem pr7_close_or_advance_gate_pack (G : PR7CloseOrAdvanceGate) :
    G.ready ↔ G.reviewGateReady ∧ G.decisionRecorded ∧ G.noAutomaticMerge := by
  rfl

end MathlibAdoptionGate
end MGAP4D
