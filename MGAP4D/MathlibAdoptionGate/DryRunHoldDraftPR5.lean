import MGAP4D.MathlibAdoptionGate.DryRunDecisionGatePR5

namespace MGAP4D
namespace MathlibAdoptionGate

structure PR5HoldDraftRecord where
  dryRunSuccessRecorded : Prop
  reviewGateRecorded : Prop
  decisionGateRecorded : Prop
  decisionIsHoldDraft : Prop
  prDraft : Prop
  prUnmerged : Prop
  mainPreMathlib : Prop
  lowerBoundDeferred : Prop
  publicBoundaryHeld : Prop

def PR5HoldDraftRecord.ready (R : PR5HoldDraftRecord) : Prop :=
  R.dryRunSuccessRecorded ∧ R.reviewGateRecorded ∧ R.decisionGateRecorded ∧
  R.decisionIsHoldDraft ∧ R.prDraft ∧ R.prUnmerged ∧
  R.mainPreMathlib ∧ R.lowerBoundDeferred ∧ R.publicBoundaryHeld

theorem pr5_hold_draft_record_pack (R : PR5HoldDraftRecord) :
    R.ready ↔ R.dryRunSuccessRecorded ∧ R.reviewGateRecorded ∧ R.decisionGateRecorded ∧
      R.decisionIsHoldDraft ∧ R.prDraft ∧ R.prUnmerged ∧
      R.mainPreMathlib ∧ R.lowerBoundDeferred ∧ R.publicBoundaryHeld := by
  rfl

end MathlibAdoptionGate
end MGAP4D
