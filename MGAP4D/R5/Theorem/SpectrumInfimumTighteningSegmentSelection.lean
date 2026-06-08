import MGAP4D.R5.Theorem.SpectrumInfimumHardeningPass
import MGAP4D.R4.Theorem.LowerBoundProofObligationTighteningClosure

namespace MGAP4D
namespace R5
namespace Theorem

inductive SpectrumInfimumTighteningSegment where
  | r5SpectrumInfimumObligation
  deriving Repr, DecidableEq

structure SpectrumInfimumTighteningSegmentSelection where
  r4TighteningClosureGreen : Prop
  spectrumInfimumHardeningPassVisible : Prop
  selectedSegment : SpectrumInfimumTighteningSegment
  selectedIsR5SpectrumInfimum : selectedSegment = SpectrumInfimumTighteningSegment.r5SpectrumInfimumObligation
  tighteningOnly : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  theoremCompletionNotClaimed : Prop
  downstreamR6R7NotUnlocked : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def SpectrumInfimumTighteningSegmentSelection.ready
    (S : SpectrumInfimumTighteningSegmentSelection) : Prop :=
  S.r4TighteningClosureGreen ∧ S.spectrumInfimumHardeningPassVisible ∧
  S.selectedSegment = SpectrumInfimumTighteningSegment.r5SpectrumInfimumObligation ∧
  S.tighteningOnly ∧ S.mainPreMathlib ∧ S.mathlibMainAdoptionHeld ∧
  S.theoremCompletionNotClaimed ∧ S.downstreamR6R7NotUnlocked ∧
  S.finalGapReleaseNotUnlocked ∧ S.publicBoundaryHeld

theorem spectrum_infimum_tightening_segment_selection_pack
    (S : SpectrumInfimumTighteningSegmentSelection) :
    S.ready ↔ S.r4TighteningClosureGreen ∧ S.spectrumInfimumHardeningPassVisible ∧
      S.selectedSegment = SpectrumInfimumTighteningSegment.r5SpectrumInfimumObligation ∧
      S.tighteningOnly ∧ S.mainPreMathlib ∧ S.mathlibMainAdoptionHeld ∧
      S.theoremCompletionNotClaimed ∧ S.downstreamR6R7NotUnlocked ∧
      S.finalGapReleaseNotUnlocked ∧ S.publicBoundaryHeld := by
  rfl

/-- The selected segment equality is still available from the stored certificate. -/
theorem spectrum_infimum_tightening_segment_selection_selected_eq
    (S : SpectrumInfimumTighteningSegmentSelection) :
    S.selectedSegment = SpectrumInfimumTighteningSegment.r5SpectrumInfimumObligation := by
  exact S.selectedIsR5SpectrumInfimum

end Theorem
end R5
end MGAP4D
