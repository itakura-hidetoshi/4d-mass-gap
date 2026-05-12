import MGAP4D.MathlibAdoptionGate.MainAdoptionReviewGate

namespace MGAP4D
namespace MathlibAdoptionGate

inductive MainAdoptionDecision where
  | holdMainAdoption
  | prepareSeparateAdoptionProposal
  | closeDryRunsWithoutMerge
  deriving Repr, DecidableEq

structure MainAdoptionHoldDecision where
  dryRunSeriesSucceeded : Prop
  reviewGateRecorded : Prop
  decision : MainAdoptionDecision
  decisionIsHold : Prop
  mainRemainsPreMathlib : Prop
  mathlibNotIntroducedToMain : Prop
  theoremRoutesRemainReviewGated : Prop
  publicBoundaryHeld : Prop
  separateDecisionRequiredForAdoption : Prop

def MainAdoptionHoldDecision.ready (D : MainAdoptionHoldDecision) : Prop :=
  D.dryRunSeriesSucceeded ∧ D.reviewGateRecorded ∧ D.decisionIsHold ∧
  D.mainRemainsPreMathlib ∧ D.mathlibNotIntroducedToMain ∧
  D.theoremRoutesRemainReviewGated ∧ D.publicBoundaryHeld ∧
  D.separateDecisionRequiredForAdoption

theorem main_adoption_hold_decision_pack (D : MainAdoptionHoldDecision) :
    D.ready ↔ D.dryRunSeriesSucceeded ∧ D.reviewGateRecorded ∧ D.decisionIsHold ∧
      D.mainRemainsPreMathlib ∧ D.mathlibNotIntroducedToMain ∧
      D.theoremRoutesRemainReviewGated ∧ D.publicBoundaryHeld ∧
      D.separateDecisionRequiredForAdoption := by
  rfl

end MathlibAdoptionGate
end MGAP4D
