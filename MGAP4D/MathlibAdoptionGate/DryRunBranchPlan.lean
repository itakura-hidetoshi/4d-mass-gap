import MGAP4D.MathlibAdoptionGate
import MGAP4D.R1.Theorem.HilbertMilestone

namespace MGAP4D
namespace MathlibAdoptionGate

structure DryRunBranchPlan where
  branchNameRecorded : Prop
  mainBranchUnchanged : Prop
  lakefileChangeIsBranchOnly : Prop
  r1HilbertMilestoneReady : Prop
  scopedRequestReady : Prop
  failureRecordedNotSilent : Prop

def DryRunBranchPlan.ready (P : DryRunBranchPlan) : Prop :=
  P.branchNameRecorded ∧ P.mainBranchUnchanged ∧ P.lakefileChangeIsBranchOnly ∧
  P.r1HilbertMilestoneReady ∧ P.scopedRequestReady ∧ P.failureRecordedNotSilent

theorem dry_run_branch_plan_pack
    (P : DryRunBranchPlan) :
    P.ready ↔ P.branchNameRecorded ∧ P.mainBranchUnchanged ∧ P.lakefileChangeIsBranchOnly ∧
      P.r1HilbertMilestoneReady ∧ P.scopedRequestReady ∧ P.failureRecordedNotSilent := by
  rfl

end MathlibAdoptionGate
end MGAP4D
