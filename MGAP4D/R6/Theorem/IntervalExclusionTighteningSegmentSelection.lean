import MGAP4D.R6.Theorem.IntervalExclusionHardeningPass
import MGAP4D.R5.Theorem.SpectrumInfimumProofObligationTighteningClosure

namespace MGAP4D
namespace R6
namespace Theorem

inductive IntervalExclusionTighteningSegment where
  | r6IntervalExclusionObligation
  deriving Repr, DecidableEq

structure IntervalExclusionTighteningSegmentSelection where
  r5ClosureGreen : Prop
  r6HardeningPassVisible : Prop
  selectedSegment : IntervalExclusionTighteningSegment
  selectedIsR6 : selectedSegment = IntervalExclusionTighteningSegment.r6IntervalExclusionObligation
  tighteningOnly : Prop
  mainPreMathlib : Prop
  mathlibAdoptionHeld : Prop
  theoremCompletionNotClaimed : Prop
  r7NotUnlocked : Prop
  publicBoundaryHeld : Prop

def IntervalExclusionTighteningSegmentSelection.ready
    (S : IntervalExclusionTighteningSegmentSelection) : Prop :=
  S.r5ClosureGreen ∧ S.r6HardeningPassVisible ∧
  S.selectedSegment = IntervalExclusionTighteningSegment.r6IntervalExclusionObligation ∧
  S.tighteningOnly ∧ S.mainPreMathlib ∧ S.mathlibAdoptionHeld ∧
  S.theoremCompletionNotClaimed ∧ S.r7NotUnlocked ∧ S.publicBoundaryHeld

theorem interval_exclusion_tightening_segment_selection_pack
    (S : IntervalExclusionTighteningSegmentSelection) :
    S.ready ↔ S.r5ClosureGreen ∧ S.r6HardeningPassVisible ∧
      S.selectedSegment = IntervalExclusionTighteningSegment.r6IntervalExclusionObligation ∧
      S.tighteningOnly ∧ S.mainPreMathlib ∧ S.mathlibAdoptionHeld ∧
      S.theoremCompletionNotClaimed ∧ S.r7NotUnlocked ∧ S.publicBoundaryHeld := by
  rfl

/-- The selected segment equality is still available from the stored certificate. -/
theorem interval_exclusion_tightening_segment_selection_selected_eq
    (S : IntervalExclusionTighteningSegmentSelection) :
    S.selectedSegment = IntervalExclusionTighteningSegment.r6IntervalExclusionObligation := by
  exact S.selectedIsR6

end Theorem
end R6
end MGAP4D
