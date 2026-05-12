import MGAP4D.MathlibAdoptionGate.DryRunDecisionGatePR6

namespace MGAP4D
namespace MathlibAdoptionGate

structure PR6HoldDraftRecord where
  dryRunSuccessRecorded : Prop
  reviewGateRecorded : Prop
  decisionGateRecorded : Prop
  decisionIsHoldDraft : Prop
  prDraft : Prop
  prUnmerged : Prop
  mainPreMathlib : Prop
  spectrumInfimumDeferred : Prop
  publicBoundaryHeld : Prop

def PR6HoldDraftRecord.ready (R : PR6HoldDraftRecord) : Prop :=
  R.dryRunSuccessRecorded ∧ R.reviewGateRecorded ∧ R.decisionGateRecorded ∧
  R.decisionIsHoldDraft ∧ R.prDraft ∧ R.prUnmerged ∧
  R.mainPreMathlib ∧ R.spectrumInfimumDeferred ∧ R.publicBoundaryHeld

theorem pr6_hold_draft_record_pack (R : PR6HoldDraftRecord) :
    R.ready ↔ R.dryRunSuccessRecorded ∧ R.reviewGateRecorded ∧ R.decisionGateRecorded ∧
      R.decisionIsHoldDraft ∧ R.prDraft ∧ R.prUnmerged ∧
      R.mainPreMathlib ∧ R.spectrumInfimumDeferred ∧ R.publicBoundaryHeld := by
  rfl

end MathlibAdoptionGate
end MGAP4D
