import MGAP4D.MathlibAdoptionGate.DryRunDecisionGatePR4

namespace MGAP4D
namespace MathlibAdoptionGate

structure PR4HoldDraftRecord where
  dryRunSuccessRecorded : Prop
  reviewGateRecorded : Prop
  decisionGateRecorded : Prop
  decisionIsHoldDraft : Prop
  prDraft : Prop
  prUnmerged : Prop
  mainPreMathlib : Prop
  zeroFormDeferred : Prop
  publicBoundaryHeld : Prop

def PR4HoldDraftRecord.ready (R : PR4HoldDraftRecord) : Prop :=
  R.dryRunSuccessRecorded ∧ R.reviewGateRecorded ∧ R.decisionGateRecorded ∧
  R.decisionIsHoldDraft ∧ R.prDraft ∧ R.prUnmerged ∧
  R.mainPreMathlib ∧ R.zeroFormDeferred ∧ R.publicBoundaryHeld

theorem pr4_hold_draft_record_pack (R : PR4HoldDraftRecord) :
    R.ready ↔ R.dryRunSuccessRecorded ∧ R.reviewGateRecorded ∧ R.decisionGateRecorded ∧
      R.decisionIsHoldDraft ∧ R.prDraft ∧ R.prUnmerged ∧
      R.mainPreMathlib ∧ R.zeroFormDeferred ∧ R.publicBoundaryHeld := by
  rfl

end MathlibAdoptionGate
end MGAP4D
