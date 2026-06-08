import MGAP4D.PostHardeningPassClosure
import MGAP4D.R3.Theorem.R3HardeningPass
import MGAP4D.PostProofObligationTighteningClosure
import MGAP4D.FinalTheoremReleaseGatePreparation
import MGAP4D.R1R2ProofObligationTighteningBridge

namespace MGAP4D

inductive TighteningSegment where
  | r3ShiftedZeroFormObligation
  | r4LowerBoundObligation
  | r5SpectrumInfimumObligation
  | r6IntervalExclusionObligation
  | r7AtomExactObligation
  deriving Repr, DecidableEq

structure PostHardeningPassTighteningSegmentSelection where
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  postHardeningPassClosureGreen : Prop
  selectedSegment : TighteningSegment
  selectedIsR3First : selectedSegment = TighteningSegment.r3ShiftedZeroFormObligation
  tighteningOnly : Prop
  theoremCompletionNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def PostHardeningPassTighteningSegmentSelection.ready
    (S : PostHardeningPassTighteningSegmentSelection) : Prop :=
  S.mainPreMathlib ∧ S.mathlibMainAdoptionHeld ∧
  S.postHardeningPassClosureGreen ∧
  S.selectedSegment = TighteningSegment.r3ShiftedZeroFormObligation ∧
  S.tighteningOnly ∧ S.theoremCompletionNotClaimed ∧
  S.finalGapReleaseNotUnlocked ∧ S.publicBoundaryHeld

theorem post_hardening_pass_tightening_segment_selection_pack
    (S : PostHardeningPassTighteningSegmentSelection) :
    S.ready ↔ S.mainPreMathlib ∧ S.mathlibMainAdoptionHeld ∧
      S.postHardeningPassClosureGreen ∧
      S.selectedSegment = TighteningSegment.r3ShiftedZeroFormObligation ∧
      S.tighteningOnly ∧ S.theoremCompletionNotClaimed ∧
      S.finalGapReleaseNotUnlocked ∧ S.publicBoundaryHeld := by
  rfl

/-- The selected segment equality is still available from the stored certificate. -/
theorem post_hardening_pass_tightening_segment_selection_selected_eq
    (S : PostHardeningPassTighteningSegmentSelection) :
    S.selectedSegment = TighteningSegment.r3ShiftedZeroFormObligation := by
  exact S.selectedIsR3First

end MGAP4D
