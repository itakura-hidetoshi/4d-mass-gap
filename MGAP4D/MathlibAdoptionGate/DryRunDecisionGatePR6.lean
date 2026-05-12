import MGAP4D.MathlibAdoptionGate.DryRunReviewGatePR6

namespace MGAP4D
namespace MathlibAdoptionGate

inductive PR6DryRunDecision where
  | holdDraft
  | closeAsSuccessfulDryRun
  | prepareReviewedAdoptionProposal
  deriving Repr, DecidableEq

structure PR6CloseAsDryRunGate where
  dryRunSuccessRecorded : Prop
  resultLedgerRecorded : Prop
  mainRemainsPreMathlib : Prop
  prClosedWithoutMerge : Prop
  futureAdoptionRequiresNewProposal : Prop

def PR6CloseAsDryRunGate.ready (G : PR6CloseAsDryRunGate) : Prop :=
  G.dryRunSuccessRecorded ∧ G.resultLedgerRecorded ∧ G.mainRemainsPreMathlib ∧
  G.prClosedWithoutMerge ∧ G.futureAdoptionRequiresNewProposal

theorem pr6_close_as_dry_run_gate_pack (G : PR6CloseAsDryRunGate) :
    G.ready ↔ G.dryRunSuccessRecorded ∧ G.resultLedgerRecorded ∧ G.mainRemainsPreMathlib ∧
      G.prClosedWithoutMerge ∧ G.futureAdoptionRequiresNewProposal := by
  rfl

structure PR6ReviewedAdoptionGate where
  dryRunSuccessRecorded : Prop
  spectrumInfimumRouteReviewed : Prop
  lakefileScopeReviewed : Prop
  manifestBehaviorReviewed : Prop
  importGroupReviewed : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop
  finalHeadCIGreen : Prop
  stillRequiresExplicitDecision : Prop

def PR6ReviewedAdoptionGate.ready (G : PR6ReviewedAdoptionGate) : Prop :=
  G.dryRunSuccessRecorded ∧ G.spectrumInfimumRouteReviewed ∧ G.lakefileScopeReviewed ∧
  G.manifestBehaviorReviewed ∧ G.importGroupReviewed ∧ G.statusSurfacesPreserved ∧
  G.publicBoundaryHeld ∧ G.finalHeadCIGreen ∧ G.stillRequiresExplicitDecision

theorem pr6_reviewed_adoption_gate_pack (G : PR6ReviewedAdoptionGate) :
    G.ready ↔ G.dryRunSuccessRecorded ∧ G.spectrumInfimumRouteReviewed ∧ G.lakefileScopeReviewed ∧
      G.manifestBehaviorReviewed ∧ G.importGroupReviewed ∧ G.statusSurfacesPreserved ∧
      G.publicBoundaryHeld ∧ G.finalHeadCIGreen ∧ G.stillRequiresExplicitDecision := by
  rfl

structure PR6CloseOrAdvanceGate where
  reviewGateReady : Prop
  decisionRecorded : Prop
  decision : PR6DryRunDecision
  noAutomaticMerge : Prop

def PR6CloseOrAdvanceGate.ready (G : PR6CloseOrAdvanceGate) : Prop :=
  G.reviewGateReady ∧ G.decisionRecorded ∧ G.noAutomaticMerge

theorem pr6_close_or_advance_gate_pack (G : PR6CloseOrAdvanceGate) :
    G.ready ↔ G.reviewGateReady ∧ G.decisionRecorded ∧ G.noAutomaticMerge := by
  rfl

end MathlibAdoptionGate
end MGAP4D
