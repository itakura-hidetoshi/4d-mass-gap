import MGAP4D.MathlibAdoptionGate.DryRunKeepDraftPR3
import MGAP4D.MathlibAdoptionGate.DryRunHoldDraftPR4
import MGAP4D.MathlibAdoptionGate.DryRunHoldDraftPR5
import MGAP4D.MathlibAdoptionGate.DryRunHoldDraftPR6
import MGAP4D.MathlibAdoptionGate.DryRunHoldDraftPR7
import MGAP4D.MathlibAdoptionGate.DryRunHoldPR8

namespace MGAP4D
namespace MathlibAdoptionGate

structure DryRunSeriesReviewR1R7 where
  r1DryRunSuccessRecorded : Prop
  r2DryRunSuccessRecorded : Prop
  r3DryRunSuccessRecorded : Prop
  r4DryRunSuccessRecorded : Prop
  r5DryRunSuccessRecorded : Prop
  r6DryRunSuccessRecorded : Prop
  r7DryRunSuccessRecorded : Prop
  allDryRunPRsUnmerged : Prop
  mainPreMathlib : Prop
  theoremRoutesReviewGated : Prop
  publicBoundaryHeld : Prop
  adoptionStillRequiresSeparateDecision : Prop

def DryRunSeriesReviewR1R7.ready (R : DryRunSeriesReviewR1R7) : Prop :=
  R.r1DryRunSuccessRecorded ∧ R.r2DryRunSuccessRecorded ∧ R.r3DryRunSuccessRecorded ∧
  R.r4DryRunSuccessRecorded ∧ R.r5DryRunSuccessRecorded ∧ R.r6DryRunSuccessRecorded ∧
  R.r7DryRunSuccessRecorded ∧ R.allDryRunPRsUnmerged ∧ R.mainPreMathlib ∧
  R.theoremRoutesReviewGated ∧ R.publicBoundaryHeld ∧ R.adoptionStillRequiresSeparateDecision

theorem dry_run_series_review_r1_r7_pack (R : DryRunSeriesReviewR1R7) :
    R.ready ↔ R.r1DryRunSuccessRecorded ∧ R.r2DryRunSuccessRecorded ∧ R.r3DryRunSuccessRecorded ∧
      R.r4DryRunSuccessRecorded ∧ R.r5DryRunSuccessRecorded ∧ R.r6DryRunSuccessRecorded ∧
      R.r7DryRunSuccessRecorded ∧ R.allDryRunPRsUnmerged ∧ R.mainPreMathlib ∧
      R.theoremRoutesReviewGated ∧ R.publicBoundaryHeld ∧ R.adoptionStillRequiresSeparateDecision := by
  rfl

end MathlibAdoptionGate
end MGAP4D
