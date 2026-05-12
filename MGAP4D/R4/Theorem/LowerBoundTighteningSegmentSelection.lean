import MGAP4D.R4.Theorem.LowerBoundHardeningPass
import MGAP4D.R3.Theorem.R3ProofObligationTighteningClosure

namespace MGAP4D
namespace R4
namespace Theorem

inductive LowerBoundTighteningSegment where
  | r4LowerBoundObligation
  deriving Repr, DecidableEq

structure LowerBoundTighteningSegmentSelection where
  r3TighteningClosureGreen : Prop
  lowerBoundHardeningPassVisible : Prop
  selectedSegment : LowerBoundTighteningSegment
  selectedIsR4LowerBound : selectedSegment = LowerBoundTighteningSegment.r4LowerBoundObligation
  tighteningOnly : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  theoremCompletionNotClaimed : Prop
  downstreamR5R7NotUnlocked : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def LowerBoundTighteningSegmentSelection.ready
    (S : LowerBoundTighteningSegmentSelection) : Prop :=
  S.r3TighteningClosureGreen ∧ S.lowerBoundHardeningPassVisible ∧
  S.selectedIsR4LowerBound ∧ S.tighteningOnly ∧
  S.mainPreMathlib ∧ S.mathlibMainAdoptionHeld ∧
  S.theoremCompletionNotClaimed ∧ S.downstreamR5R7NotUnlocked ∧
  S.finalGapReleaseNotUnlocked ∧ S.publicBoundaryHeld

theorem lower_bound_tightening_segment_selection_pack
    (S : LowerBoundTighteningSegmentSelection) :
    S.ready ↔ S.r3TighteningClosureGreen ∧ S.lowerBoundHardeningPassVisible ∧
      S.selectedIsR4LowerBound ∧ S.tighteningOnly ∧
      S.mainPreMathlib ∧ S.mathlibMainAdoptionHeld ∧
      S.theoremCompletionNotClaimed ∧ S.downstreamR5R7NotUnlocked ∧
      S.finalGapReleaseNotUnlocked ∧ S.publicBoundaryHeld := by
  rfl

end Theorem
end R4
end MGAP4D
