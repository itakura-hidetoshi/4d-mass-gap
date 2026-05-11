import MGAP4D.MathlibAdoptionGate.DryRunReviewGatePR1

namespace MGAP4D
namespace MathlibAdoptionGate

inductive PR1DryRunDecision where
  | keepDraft
  | closeAsSuccessfulDryRun
  | promoteToMergeProposal
  deriving Repr, DecidableEq

structure PR1CloseAsDryRunGate where
  dryRunSuccessRecorded : Prop
  resultLedgerRecorded : Prop
  mainRemainsPreMathlib : Prop
  prClosedWithoutMerge : Prop
  futureAdoptionRequiresNewProposal : Prop

def PR1CloseAsDryRunGate.ready (G : PR1CloseAsDryRunGate) : Prop :=
  G.dryRunSuccessRecorded ∧ G.resultLedgerRecorded ∧ G.mainRemainsPreMathlib ∧
  G.prClosedWithoutMerge ∧ G.futureAdoptionRequiresNewProposal

theorem pr1_close_as_dry_run_gate_pack
    (G : PR1CloseAsDryRunGate) :
    G.ready ↔ G.dryRunSuccessRecorded ∧ G.resultLedgerRecorded ∧ G.mainRemainsPreMathlib ∧
      G.prClosedWithoutMerge ∧ G.futureAdoptionRequiresNewProposal := by
  rfl

structure PR1PromoteToMergeGate where
  dryRunSuccessRecorded : Prop
  lakefileScopeReviewed : Prop
  manifestBehaviorReviewed : Prop
  importGroupReviewed : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop
  finalHeadCIGreen : Prop
  mergeStillNotAutomatic : Prop

def PR1PromoteToMergeGate.ready (G : PR1PromoteToMergeGate) : Prop :=
  G.dryRunSuccessRecorded ∧ G.lakefileScopeReviewed ∧ G.manifestBehaviorReviewed ∧
  G.importGroupReviewed ∧ G.statusSurfacesPreserved ∧ G.publicBoundaryHeld ∧
  G.finalHeadCIGreen ∧ G.mergeStillNotAutomatic

theorem pr1_promote_to_merge_gate_pack
    (G : PR1PromoteToMergeGate) :
    G.ready ↔ G.dryRunSuccessRecorded ∧ G.lakefileScopeReviewed ∧ G.manifestBehaviorReviewed ∧
      G.importGroupReviewed ∧ G.statusSurfacesPreserved ∧ G.publicBoundaryHeld ∧
      G.finalHeadCIGreen ∧ G.mergeStillNotAutomatic := by
  rfl

structure PR1CloseOrPromoteGate where
  reviewGateReady : Prop
  decisionRecorded : Prop
  decision : PR1DryRunDecision
  noAutomaticMerge : Prop

def PR1CloseOrPromoteGate.ready (G : PR1CloseOrPromoteGate) : Prop :=
  G.reviewGateReady ∧ G.decisionRecorded ∧ G.noAutomaticMerge

theorem pr1_close_or_promote_gate_pack
    (G : PR1CloseOrPromoteGate) :
    G.ready ↔ G.reviewGateReady ∧ G.decisionRecorded ∧ G.noAutomaticMerge := by
  rfl

end MathlibAdoptionGate
end MGAP4D
