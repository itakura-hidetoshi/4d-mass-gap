import MGAP4D.R2.Theorem.RestrictionSkeleton
import MGAP4D.R1.Theorem.HilbertProofObligationTighteningClosure
import MGAP4D.R1R2ProofObligationTighteningBridge

namespace MGAP4D
namespace R2
namespace Theorem

inductive RestrictionTighteningSegment where
  | r2RestrictionObligation
  deriving Repr, DecidableEq

structure RestrictionTighteningSegmentSelection where
  r1ClosureGreen : Prop
  r1r2BridgeGreen : Prop
  restrictionSkeletonVisible : Prop
  selectedSegment : RestrictionTighteningSegment
  selectedIsR2Restriction : selectedSegment = RestrictionTighteningSegment.r2RestrictionObligation
  r1ClosurePreserved : Prop
  tighteningOnly : Prop
  mainPreMathlib : Prop
  mathlibAdoptionHeld : Prop
  r2TheoremCompletionNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def RestrictionTighteningSegmentSelection.ready
    (S : RestrictionTighteningSegmentSelection) : Prop :=
  S.r1ClosureGreen ∧ S.r1r2BridgeGreen ∧ S.restrictionSkeletonVisible ∧
  S.selectedIsR2Restriction ∧ S.r1ClosurePreserved ∧ S.tighteningOnly ∧
  S.mainPreMathlib ∧ S.mathlibAdoptionHeld ∧ S.r2TheoremCompletionNotClaimed ∧
  S.finalGapReleaseNotUnlocked ∧ S.publicBoundaryHeld

theorem restriction_tightening_segment_selection_pack
    (S : RestrictionTighteningSegmentSelection) :
    S.ready ↔ S.r1ClosureGreen ∧ S.r1r2BridgeGreen ∧ S.restrictionSkeletonVisible ∧
      S.selectedIsR2Restriction ∧ S.r1ClosurePreserved ∧ S.tighteningOnly ∧
      S.mainPreMathlib ∧ S.mathlibAdoptionHeld ∧ S.r2TheoremCompletionNotClaimed ∧
      S.finalGapReleaseNotUnlocked ∧ S.publicBoundaryHeld := by
  rfl

end Theorem
end R2
end MGAP4D
