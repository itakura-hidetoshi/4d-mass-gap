import MGAP4D.R5.Theorem.SpectrumInfimumTighteningSegmentSelection
import MGAP4D.R5.Theorem.SpectrumSkeleton

namespace MGAP4D
namespace R5
namespace Theorem

structure SpectrumInfimumProofObligationTighteningPass1 where
  segmentSelectionGreen : Prop
  theoremSkeletonVisible : Prop
  spectrumSetObligationSeparated : Prop
  spectrumBottomObligationSeparated : Prop
  witnessObligationSeparated : Prop
  comparisonObligationSeparated : Prop
  infimumObligationSeparated : Prop
  upstreamR4LowerBoundDependencySeparated : Prop
  upstreamR3ZeroFormDependencySeparated : Prop
  downstreamR6R7ReviewGateSeparated : Prop
  mathlibRequestBoundarySeparated : Prop
  publicBoundaryObligationSeparated : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  theoremCompletionNotClaimed : Prop
  downstreamR6R7NotUnlocked : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def SpectrumInfimumProofObligationTighteningPass1.ready
    (P : SpectrumInfimumProofObligationTighteningPass1) : Prop :=
  P.segmentSelectionGreen ∧ P.theoremSkeletonVisible ∧
  P.spectrumSetObligationSeparated ∧ P.spectrumBottomObligationSeparated ∧
  P.witnessObligationSeparated ∧ P.comparisonObligationSeparated ∧
  P.infimumObligationSeparated ∧ P.upstreamR4LowerBoundDependencySeparated ∧
  P.upstreamR3ZeroFormDependencySeparated ∧ P.downstreamR6R7ReviewGateSeparated ∧
  P.mathlibRequestBoundarySeparated ∧ P.publicBoundaryObligationSeparated ∧
  P.mainPreMathlib ∧ P.mathlibMainAdoptionHeld ∧ P.theoremCompletionNotClaimed ∧
  P.downstreamR6R7NotUnlocked ∧ P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld

theorem spectrum_infimum_proof_obligation_tightening_pass1_pack
    (P : SpectrumInfimumProofObligationTighteningPass1) :
    P.ready ↔ P.segmentSelectionGreen ∧ P.theoremSkeletonVisible ∧
      P.spectrumSetObligationSeparated ∧ P.spectrumBottomObligationSeparated ∧
      P.witnessObligationSeparated ∧ P.comparisonObligationSeparated ∧
      P.infimumObligationSeparated ∧ P.upstreamR4LowerBoundDependencySeparated ∧
      P.upstreamR3ZeroFormDependencySeparated ∧ P.downstreamR6R7ReviewGateSeparated ∧
      P.mathlibRequestBoundarySeparated ∧ P.publicBoundaryObligationSeparated ∧
      P.mainPreMathlib ∧ P.mathlibMainAdoptionHeld ∧ P.theoremCompletionNotClaimed ∧
      P.downstreamR6R7NotUnlocked ∧ P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld := by
  rfl

end Theorem
end R5
end MGAP4D
