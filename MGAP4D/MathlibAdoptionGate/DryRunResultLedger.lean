import MGAP4D.MathlibAdoptionGate.DryRunChecklist

namespace MGAP4D
namespace MathlibAdoptionGate

inductive DryRunOutcome where
  | success
  | failure
  | blocked
  deriving Repr, DecidableEq

structure DryRunResultRecord where
  branchNameRecorded : Prop
  requesterRecorded : Prop
  plannedImportGroupRecorded : Prop
  actualImportGroupRecorded : Prop
  lakeUpdateResultRecorded : Prop
  lakeBuildResultRecorded : Prop
  checkScriptResultRecorded : Prop
  statusSurfacePreservationRecorded : Prop
  publicBoundaryResultRecorded : Prop
  outcome : DryRunOutcome
  failureSummaryRecorded : Prop
  reviewNoteRecordedIfSucceeded : Prop
  mergeGateStatusRecorded : Prop

def DryRunResultRecord.ready (R : DryRunResultRecord) : Prop :=
  R.branchNameRecorded ∧ R.requesterRecorded ∧ R.plannedImportGroupRecorded ∧
  R.actualImportGroupRecorded ∧ R.lakeUpdateResultRecorded ∧ R.lakeBuildResultRecorded ∧
  R.checkScriptResultRecorded ∧ R.statusSurfacePreservationRecorded ∧
  R.publicBoundaryResultRecorded ∧ R.failureSummaryRecorded ∧
  R.reviewNoteRecordedIfSucceeded ∧ R.mergeGateStatusRecorded

theorem dry_run_result_record_pack
    (R : DryRunResultRecord) :
    R.ready ↔ R.branchNameRecorded ∧ R.requesterRecorded ∧ R.plannedImportGroupRecorded ∧
      R.actualImportGroupRecorded ∧ R.lakeUpdateResultRecorded ∧ R.lakeBuildResultRecorded ∧
      R.checkScriptResultRecorded ∧ R.statusSurfacePreservationRecorded ∧
      R.publicBoundaryResultRecorded ∧ R.failureSummaryRecorded ∧
      R.reviewNoteRecordedIfSucceeded ∧ R.mergeGateStatusRecorded := by
  rfl

structure DryRunResultLedger where
  atLeastOneRecordOrExplicitNone : Prop
  failuresAreRecorded : Prop
  successesRequireReviewNote : Prop
  mainMutationForbiddenOnFailure : Prop
  mergeStillGated : Prop

def DryRunResultLedger.ready (L : DryRunResultLedger) : Prop :=
  L.atLeastOneRecordOrExplicitNone ∧ L.failuresAreRecorded ∧
  L.successesRequireReviewNote ∧ L.mainMutationForbiddenOnFailure ∧ L.mergeStillGated

theorem dry_run_result_ledger_pack
    (L : DryRunResultLedger) :
    L.ready ↔ L.atLeastOneRecordOrExplicitNone ∧ L.failuresAreRecorded ∧
      L.successesRequireReviewNote ∧ L.mainMutationForbiddenOnFailure ∧ L.mergeStillGated := by
  rfl

end MathlibAdoptionGate
end MGAP4D
