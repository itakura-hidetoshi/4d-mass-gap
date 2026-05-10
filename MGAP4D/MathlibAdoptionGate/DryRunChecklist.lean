import MGAP4D.MathlibAdoptionGate.DryRunGate

namespace MGAP4D
namespace MathlibAdoptionGate

structure DryRunPreBranchChecklist where
  pass2ClosureRecorded : Prop
  preMathlibGateRecorded : Prop
  mathlibGateRecorded : Prop
  dryRunPlanRecorded : Prop
  dryRunGateRecorded : Prop
  r1HilbertRequestScoped : Prop
  r1HilbertMilestoneReady : Prop
  mainBranchClean : Prop
  ciGreenOrFailureRecorded : Prop
  publicBoundaryHeld : Prop

def DryRunPreBranchChecklist.ready (C : DryRunPreBranchChecklist) : Prop :=
  C.pass2ClosureRecorded ∧ C.preMathlibGateRecorded ∧ C.mathlibGateRecorded ∧
  C.dryRunPlanRecorded ∧ C.dryRunGateRecorded ∧ C.r1HilbertRequestScoped ∧
  C.r1HilbertMilestoneReady ∧ C.mainBranchClean ∧ C.ciGreenOrFailureRecorded ∧
  C.publicBoundaryHeld

theorem dry_run_pre_branch_checklist_pack
    (C : DryRunPreBranchChecklist) :
    C.ready ↔ C.pass2ClosureRecorded ∧ C.preMathlibGateRecorded ∧ C.mathlibGateRecorded ∧
      C.dryRunPlanRecorded ∧ C.dryRunGateRecorded ∧ C.r1HilbertRequestScoped ∧
      C.r1HilbertMilestoneReady ∧ C.mainBranchClean ∧ C.ciGreenOrFailureRecorded ∧
      C.publicBoundaryHeld := by
  rfl

structure DryRunBranchChecklist where
  lakefileChangedOnBranchOnly : Prop
  lakeUpdateRun : Prop
  manifestCommittedOnlyIfGenerated : Prop
  mathlibSpecificModuleAdded : Prop
  checkScriptRun : Prop
  buildResultRecorded : Prop
  actualImportGroupRecorded : Prop
  statusSurfacesPreserved : Prop
  publicBoundaryHeld : Prop

def DryRunBranchChecklist.ready (C : DryRunBranchChecklist) : Prop :=
  C.lakefileChangedOnBranchOnly ∧ C.lakeUpdateRun ∧ C.manifestCommittedOnlyIfGenerated ∧
  C.mathlibSpecificModuleAdded ∧ C.checkScriptRun ∧ C.buildResultRecorded ∧
  C.actualImportGroupRecorded ∧ C.statusSurfacesPreserved ∧ C.publicBoundaryHeld

theorem dry_run_branch_checklist_pack
    (C : DryRunBranchChecklist) :
    C.ready ↔ C.lakefileChangedOnBranchOnly ∧ C.lakeUpdateRun ∧ C.manifestCommittedOnlyIfGenerated ∧
      C.mathlibSpecificModuleAdded ∧ C.checkScriptRun ∧ C.buildResultRecorded ∧
      C.actualImportGroupRecorded ∧ C.statusSurfacesPreserved ∧ C.publicBoundaryHeld := by
  rfl

structure DryRunOutcomeRule where
  failureRecordedNotSilent : Prop
  mainRemainsUnchangedOnFailure : Prop
  reviewNoteRequiredOnSuccess : Prop
  mergeStillGated : Prop

def DryRunOutcomeRule.ready (R : DryRunOutcomeRule) : Prop :=
  R.failureRecordedNotSilent ∧ R.mainRemainsUnchangedOnFailure ∧
  R.reviewNoteRequiredOnSuccess ∧ R.mergeStillGated

theorem dry_run_outcome_rule_pack
    (R : DryRunOutcomeRule) :
    R.ready ↔ R.failureRecordedNotSilent ∧ R.mainRemainsUnchangedOnFailure ∧
      R.reviewNoteRequiredOnSuccess ∧ R.mergeStillGated := by
  rfl

end MathlibAdoptionGate
end MGAP4D
