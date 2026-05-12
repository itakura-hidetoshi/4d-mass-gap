import MGAP4D.MathlibAdoptionGate.DryRunReviewGatePR3

namespace MGAP4D
namespace MathlibAdoptionGate

inductive PR3DryRunDecision where
  | keepDraft
  | closeAsSuccessfulDryRun
  | prepareReviewedAdoptionProposal
  deriving Repr, DecidableEq

structure PR3CloseAsDryRunGate where
  dryRunSuccessRecorded : Prop
  resultLedgerRecorded : Prop
  mainRemainsPreMathlib : Prop
  prClosedWithoutMerge : Prop
  futureAdoptionRequiresNewProposal : Prop

def PR3CloseAsDryRunGate.ready (G : PR3CloseAsDryRunGate) : Prop :=
  G.dryRunSuccessRecorded ∧ G.resultLedgerRecorded ∧ G.mainRemainsPreMathlib ∧
  G.prClosedWithoutMerge ∧ G.futureAdoptionRequiresNewProposal

theorem pr3_close_as_dry_run_gate_pack (G : PR3CloseAsDryRunGate) :
    G.ready ↔ G.dryRunSuccessRecorded ∧ G.resultLedgerRecorded ∧ G.mainRemainsPreMathlib ∧
      G.prClosedWithoutMerge ∧ G.futureAdoptionRequiresNewProposal := by
  rfl

structure PR3ReviewedAdoptionGate where
  dryRunSuccessRecorded : Prop
  lakefileScopeReviewed : Prop
  manifestBehaviorReviewed : Prop
  importGroupReviewed : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop
  finalHeadCIGreen : Prop
  stillRequiresExplicitDecision : Prop

def PR3ReviewedAdoptionGate.ready (G : PR3ReviewedAdoptionGate) : Prop :=
  G.dryRunSuccessRecorded ∧ G.lakefileScopeReviewed ∧ G.manifestBehaviorReviewed ∧
  G.importGroupReviewed ∧ G.statusSurfacesPreserved ∧ G.publicBoundaryHeld ∧
  G.finalHeadCIGreen ∧ G.stillRequiresExplicitDecision

theorem pr3_reviewed_adoption_gate_pack (G : PR3ReviewedAdoptionGate) :
    G.ready ↔ G.dryRunSuccessRecorded ∧ G.lakefileScopeReviewed ∧ G.manifestBehaviorReviewed ∧
      G.importGroupReviewed ∧ G.statusSurfacesPreserved ∧ G.publicBoundaryHeld ∧
      G.finalHeadCIGreen ∧ G.stillRequiresExplicitDecision := by
  rfl

structure PR3CloseOrAdvanceGate where
  reviewGateReady : Prop
  decisionRecorded : Prop
  decision : PR3DryRunDecision
  noAutomaticMerge : Prop

def PR3CloseOrAdvanceGate.ready (G : PR3CloseOrAdvanceGate) : Prop :=
  G.reviewGateReady ∧ G.decisionRecorded ∧ G.noAutomaticMerge

theorem pr3_close_or_advance_gate_pack (G : PR3CloseOrAdvanceGate) :
    G.ready ↔ G.reviewGateReady ∧ G.decisionRecorded ∧ G.noAutomaticMerge := by
  rfl

end MathlibAdoptionGate
end MGAP4D
