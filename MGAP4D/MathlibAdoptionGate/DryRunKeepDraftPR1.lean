import MGAP4D.MathlibAdoptionGate.DryRunCloseOrPromoteGatePR1

namespace MGAP4D
namespace MathlibAdoptionGate

structure PR1KeepDraftRecord where
  dryRunSuccessRecorded : Prop
  reviewGateRecorded : Prop
  closeOrPromoteGateRecorded : Prop
  decisionIsKeepDraft : Prop
  prRemainsDraft : Prop
  prRemainsUnmerged : Prop
  mainRemainsPreMathlib : Prop
  publicBoundaryHeld : Prop

def PR1KeepDraftRecord.ready (R : PR1KeepDraftRecord) : Prop :=
  R.dryRunSuccessRecorded ∧ R.reviewGateRecorded ∧ R.closeOrPromoteGateRecorded ∧
  R.decisionIsKeepDraft ∧ R.prRemainsDraft ∧ R.prRemainsUnmerged ∧
  R.mainRemainsPreMathlib ∧ R.publicBoundaryHeld

theorem pr1_keep_draft_record_pack
    (R : PR1KeepDraftRecord) :
    R.ready ↔ R.dryRunSuccessRecorded ∧ R.reviewGateRecorded ∧ R.closeOrPromoteGateRecorded ∧
      R.decisionIsKeepDraft ∧ R.prRemainsDraft ∧ R.prRemainsUnmerged ∧
      R.mainRemainsPreMathlib ∧ R.publicBoundaryHeld := by
  rfl

end MathlibAdoptionGate
end MGAP4D
