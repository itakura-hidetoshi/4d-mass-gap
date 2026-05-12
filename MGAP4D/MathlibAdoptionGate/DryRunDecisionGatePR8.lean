import MGAP4D.MathlibAdoptionGate.DryRunReviewGatePR8

namespace MGAP4D
namespace MathlibAdoptionGate

inductive PR8DryRunDecision where
  | holdDraft
  | closeAsSuccessfulDryRun
  | prepareReviewedAdoptionProposal
  deriving Repr, DecidableEq

structure PR8CloseAsDryRunGate where
  dryRunSuccessRecorded : Prop
  resultLedgerRecorded : Prop
  mainRemainsPreMathlib : Prop
  prClosedWithoutMerge : Prop
  futureAdoptionRequiresNewProposal : Prop

def PR8CloseAsDryRunGate.ready (G : PR8CloseAsDryRunGate) : Prop :=
  G.dryRunSuccessRecorded ∧ G.resultLedgerRecorded ∧ G.mainRemainsPreMathlib ∧
  G.prClosedWithoutMerge ∧ G.futureAdoptionRequiresNewProposal

theorem pr8_close_as_dry_run_gate_pack (G : PR8CloseAsDryRunGate) :
    G.ready ↔ G.dryRunSuccessRecorded ∧ G.resultLedgerRecorded ∧ G.mainRemainsPreMathlib ∧
      G.prClosedWithoutMerge ∧ G.futureAdoptionRequiresNewProposal := by
  rfl

structure PR8ReviewedAdoptionGate where
  dryRunSuccessRecorded : Prop
  atomExactGapRouteReviewed : Prop
  lakefileScopeReviewed : Prop
  manifestBehaviorReviewed : Prop
  importGroupReviewed : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop
  finalHeadCIGreen : Prop
  stillRequiresExplicitDecision : Prop

def PR8ReviewedAdoptionGate.ready (G : PR8ReviewedAdoptionGate) : Prop :=
  G.dryRunSuccessRecorded ∧ G.atomExactGapRouteReviewed ∧ G.lakefileScopeReviewed ∧
  G.manifestBehaviorReviewed ∧ G.importGroupReviewed ∧ G.statusSurfacesPreserved ∧
  G.publicBoundaryHeld ∧ G.finalHeadCIGreen ∧ G.stillRequiresExplicitDecision

theorem pr8_reviewed_adoption_gate_pack (G : PR8ReviewedAdoptionGate) :
    G.ready ↔ G.dryRunSuccessRecorded ∧ G.atomExactGapRouteReviewed ∧ G.lakefileScopeReviewed ∧
      G.manifestBehaviorReviewed ∧ G.importGroupReviewed ∧ G.statusSurfacesPreserved ∧
      G.publicBoundaryHeld ∧ G.finalHeadCIGreen ∧ G.stillRequiresExplicitDecision := by
  rfl

structure PR8CloseOrAdvanceGate where
  reviewGateReady : Prop
  decisionRecorded : Prop
  decision : PR8DryRunDecision
  noAutomaticMerge : Prop

def PR8CloseOrAdvanceGate.ready (G : PR8CloseOrAdvanceGate) : Prop :=
  G.reviewGateReady ∧ G.decisionRecorded ∧ G.noAutomaticMerge

theorem pr8_close_or_advance_gate_pack (G : PR8CloseOrAdvanceGate) :
    G.ready ↔ G.reviewGateReady ∧ G.decisionRecorded ∧ G.noAutomaticMerge := by
  rfl

end MathlibAdoptionGate
end MGAP4D
