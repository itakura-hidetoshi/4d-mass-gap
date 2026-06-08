import MGAP4D.R1.Theorem.HilbertSkeleton
import MGAP4D.R1R2ProofObligationTighteningBridge

namespace MGAP4D
namespace R1
namespace Theorem

inductive HilbertTighteningSegment where
  | r1HilbertObligation
  deriving Repr, DecidableEq

structure HilbertTighteningSegmentSelection where
  r1r2BridgeGreen : Prop
  hilbertSkeletonVisible : Prop
  selectedSegment : HilbertTighteningSegment
  selectedIsR1Hilbert : selectedSegment = HilbertTighteningSegment.r1HilbertObligation
  r2QueuedAfterR1 : Prop
  tighteningOnly : Prop
  mainPreMathlib : Prop
  mathlibAdoptionHeld : Prop
  r1TheoremCompletionNotClaimed : Prop
  r2TheoremCompletionNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def HilbertTighteningSegmentSelection.ready
    (S : HilbertTighteningSegmentSelection) : Prop :=
  S.r1r2BridgeGreen ∧ S.hilbertSkeletonVisible ∧
  S.selectedSegment = HilbertTighteningSegment.r1HilbertObligation ∧
  S.r2QueuedAfterR1 ∧ S.tighteningOnly ∧ S.mainPreMathlib ∧
  S.mathlibAdoptionHeld ∧ S.r1TheoremCompletionNotClaimed ∧
  S.r2TheoremCompletionNotClaimed ∧ S.finalGapReleaseNotUnlocked ∧
  S.publicBoundaryHeld

theorem hilbert_tightening_segment_selection_pack
    (S : HilbertTighteningSegmentSelection) :
    S.ready ↔ S.r1r2BridgeGreen ∧ S.hilbertSkeletonVisible ∧
      S.selectedSegment = HilbertTighteningSegment.r1HilbertObligation ∧
      S.r2QueuedAfterR1 ∧ S.tighteningOnly ∧ S.mainPreMathlib ∧
      S.mathlibAdoptionHeld ∧ S.r1TheoremCompletionNotClaimed ∧
      S.r2TheoremCompletionNotClaimed ∧ S.finalGapReleaseNotUnlocked ∧
      S.publicBoundaryHeld := by
  rfl

/-- The selected segment equality is still available from the stored certificate. -/
theorem hilbert_tightening_segment_selection_selected_eq
    (S : HilbertTighteningSegmentSelection) :
    S.selectedSegment = HilbertTighteningSegment.r1HilbertObligation := by
  exact S.selectedIsR1Hilbert

end Theorem
end R1
end MGAP4D
