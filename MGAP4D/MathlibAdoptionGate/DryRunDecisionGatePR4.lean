import MGAP4D.MathlibAdoptionGate.DryRunReviewGatePR4

namespace MGAP4D
namespace MathlibAdoptionGate

inductive PR4DryRunDecision where
  | keepDraft
  | closeAsSuccessfulDryRun
  | prepareReviewedAdoptionProposal
  deriving Repr, DecidableEq

structure PR4CloseAsDryRunGate where
  dryRunSuccessRecorded : Prop
  resultLedgerRecorded : Prop
  mainRemainsPreMathlib : Prop
  prClosedWithoutMerge : Prop
  futureAdoptionRequiresNewProposal : Prop

def PR4CloseAsDryRunGate.ready (G : PR4CloseAsDryRunGate) : Prop :=
  G.dryRunSuccessRecorded ∧ G.resultLedgerRecorded ∧ G.mainRemainsPreMathlib ∧
  G.prClosedWithoutMerge ∧ G.futureAdoptionRequiresNewProposal

theorem pr4_close_as_dry_run_gate_pack (G : PR4CloseAsDryRunGate) :
    G.ready ↔ G.dryRunSuccessRecorded ∧ G.resultLedgerRecorded ∧ G.mainRemainsPreMathlib ∧
      G.prClosedWithoutMerge ∧ G.futureAdoptionRequiresNewProposal := by
  rfl

structure PR4ReviewedAdoptionGate where
  dryRunSuccessRecorded : Prop
  zeroFormRouteReviewed : Prop
  lakefileScopeReviewed : Prop
  manifestBehaviorReviewed : Prop
  importGroupReviewed : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop
  finalHeadCIGreen : Prop
  stillRequiresExplicitDecision : Prop

def PR4ReviewedAdoptionGate.ready (G : PR4ReviewedAdoptionGate) : Prop :=
  G.dryRunSuccessRecorded ∧ G.zeroFormRouteReviewed ∧ G.lakefileScopeReviewed ∧
  G.manifestBehaviorReviewed ∧ G.importGroupReviewed ∧ G.statusSurfacesPreserved ∧
  G.publicBoundaryHeld ∧ G.finalHeadCIGreen ∧ G.stillRequiresExplicitDecision

theorem pr4_reviewed_adoption_gate_pack (G : PR4ReviewedAdoptionGate) :
    G.ready ↔ G.dryRunSuccessRecorded ∧ G.zeroFormRouteReviewed ∧ G.lakefileScopeReviewed ∧
      G.manifestBehaviorReviewed ∧ G.importGroupReviewed ∧ G.statusSurfacesPreserved ∧
      G.publicBoundaryHeld ∧ G.finalHeadCIGreen ∧ G.stillRequiresExplicitDecision := by
  rfl

structure PR4CloseOrAdvanceGate where
  reviewGateReady : Prop
  decisionRecorded : Prop
  decision : PR4DryRunDecision
  noAutomaticMerge : Prop

def PR4CloseOrAdvanceGate.ready (G : PR4CloseOrAdvanceGate) : Prop :=
  G.reviewGateReady ∧ G.decisionRecorded ∧ G.noAutomaticMerge

theorem pr4_close_or_advance_gate_pack (G : PR4CloseOrAdvanceGate) :
    G.ready ↔ G.reviewGateReady ∧ G.decisionRecorded ∧ G.noAutomaticMerge := by
  rfl

end MathlibAdoptionGate
end MGAP4D
