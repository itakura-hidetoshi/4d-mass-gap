import MGAP4D.MathlibAdoptionGate.DryRunCloseOrPromoteGatePR3

namespace MGAP4D
namespace MathlibAdoptionGate

structure PR3KeepDraftRecord where
  dryRunSuccessRecorded : Prop
  reviewGateRecorded : Prop
  decisionGateRecorded : Prop
  decisionIsKeepDraft : Prop
  prRemainsDraft : Prop
  prRemainsUnmerged : Prop
  mainRemainsPreMathlib : Prop
  publicBoundaryHeld : Prop

def PR3KeepDraftRecord.ready (R : PR3KeepDraftRecord) : Prop :=
  R.dryRunSuccessRecorded ∧ R.reviewGateRecorded ∧ R.decisionGateRecorded ∧
  R.decisionIsKeepDraft ∧ R.prRemainsDraft ∧ R.prRemainsUnmerged ∧
  R.mainRemainsPreMathlib ∧ R.publicBoundaryHeld

theorem pr3_keep_draft_record_pack (R : PR3KeepDraftRecord) :
    R.ready ↔ R.dryRunSuccessRecorded ∧ R.reviewGateRecorded ∧ R.decisionGateRecorded ∧
      R.decisionIsKeepDraft ∧ R.prRemainsDraft ∧ R.prRemainsUnmerged ∧
      R.mainRemainsPreMathlib ∧ R.publicBoundaryHeld := by
  rfl

end MathlibAdoptionGate
end MGAP4D
