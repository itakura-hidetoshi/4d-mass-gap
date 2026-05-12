import MGAP4D.MathlibAdoptionGate.DryRunDecisionGatePR8

namespace MGAP4D
namespace MathlibAdoptionGate

structure PR8HoldRecord where
  dryRunSuccess : Prop
  reviewRecorded : Prop
  decisionRecorded : Prop
  holdDecision : Prop
  prDraft : Prop
  prUnmerged : Prop
  mainPreMathlib : Prop
  atomExactDeferred : Prop
  publicBoundaryHeld : Prop

def PR8HoldRecord.ready (R : PR8HoldRecord) : Prop :=
  R.dryRunSuccess ∧ R.reviewRecorded ∧ R.decisionRecorded ∧
  R.holdDecision ∧ R.prDraft ∧ R.prUnmerged ∧
  R.mainPreMathlib ∧ R.atomExactDeferred ∧ R.publicBoundaryHeld

theorem pr8_hold_record_pack (R : PR8HoldRecord) :
    R.ready ↔ R.dryRunSuccess ∧ R.reviewRecorded ∧ R.decisionRecorded ∧
      R.holdDecision ∧ R.prDraft ∧ R.prUnmerged ∧
      R.mainPreMathlib ∧ R.atomExactDeferred ∧ R.publicBoundaryHeld := by
  rfl

end MathlibAdoptionGate
end MGAP4D
