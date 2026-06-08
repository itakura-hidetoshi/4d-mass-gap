import MGAP4D.R7.Theorem.AtomExactHardeningPass
import MGAP4D.R6.Theorem.IntervalExclusionProofObligationTighteningClosure

namespace MGAP4D
namespace R7
namespace Theorem

inductive AtomExactTighteningSegment where
  | r7AtomExactObligation
  deriving Repr, DecidableEq

structure AtomExactTighteningSegmentSelection where
  r6ClosureGreen : Prop
  r7HardeningPassVisible : Prop
  selectedSegment : AtomExactTighteningSegment
  selectedIsR7 : selectedSegment = AtomExactTighteningSegment.r7AtomExactObligation
  tighteningOnly : Prop
  mainPreMathlib : Prop
  mathlibAdoptionHeld : Prop
  theoremCompletionNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def AtomExactTighteningSegmentSelection.ready
    (S : AtomExactTighteningSegmentSelection) : Prop :=
  S.r6ClosureGreen ∧ S.r7HardeningPassVisible ∧
  S.selectedSegment = AtomExactTighteningSegment.r7AtomExactObligation ∧
  S.tighteningOnly ∧ S.mainPreMathlib ∧ S.mathlibAdoptionHeld ∧
  S.theoremCompletionNotClaimed ∧ S.finalGapReleaseNotUnlocked ∧ S.publicBoundaryHeld

theorem atom_exact_tightening_segment_selection_pack
    (S : AtomExactTighteningSegmentSelection) :
    S.ready ↔ S.r6ClosureGreen ∧ S.r7HardeningPassVisible ∧
      S.selectedSegment = AtomExactTighteningSegment.r7AtomExactObligation ∧
      S.tighteningOnly ∧ S.mainPreMathlib ∧ S.mathlibAdoptionHeld ∧
      S.theoremCompletionNotClaimed ∧ S.finalGapReleaseNotUnlocked ∧ S.publicBoundaryHeld := by
  rfl

/-- The selected segment equality is still available from the stored certificate. -/
theorem atom_exact_tightening_segment_selection_selected_eq
    (S : AtomExactTighteningSegmentSelection) :
    S.selectedSegment = AtomExactTighteningSegment.r7AtomExactObligation := by
  exact S.selectedIsR7

end Theorem
end R7
end MGAP4D
