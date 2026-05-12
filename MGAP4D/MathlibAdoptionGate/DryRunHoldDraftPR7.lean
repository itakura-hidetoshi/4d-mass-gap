import MGAP4D.MathlibAdoptionGate.DryRunDecisionGatePR7

namespace MGAP4D
namespace MathlibAdoptionGate

structure PR7HoldDraftRecord where
  dryRunSuccessRecorded : Prop
  reviewGateRecorded : Prop
  decisionGateRecorded : Prop
  decisionIsHoldDraft : Prop
  prDraft : Prop
  prUnmerged : Prop
  mainPreMathlib : Prop
  intervalExclusionDeferred : Prop
  publicBoundaryHeld : Prop

def PR7HoldDraftRecord.ready (R : PR7HoldDraftRecord) : Prop :=
  R.dryRunSuccessRecorded ∧ R.reviewGateRecorded ∧ R.decisionGateRecorded ∧
  R.decisionIsHoldDraft ∧ R.prDraft ∧ R.prUnmerged ∧
  R.mainPreMathlib ∧ R.intervalExclusionDeferred ∧ R.publicBoundaryHeld

theorem pr7_hold_draft_record_pack (R : PR7HoldDraftRecord) :
    R.ready ↔ R.dryRunSuccessRecorded ∧ R.reviewGateRecorded ∧ R.decisionGateRecorded ∧
      R.decisionIsHoldDraft ∧ R.prDraft ∧ R.prUnmerged ∧
      R.mainPreMathlib ∧ R.intervalExclusionDeferred ∧ R.publicBoundaryHeld := by
  rfl

end MathlibAdoptionGate
end MGAP4D
