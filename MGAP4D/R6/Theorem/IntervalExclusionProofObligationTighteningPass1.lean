import MGAP4D.R6.Theorem.IntervalExclusionTighteningSegmentSelection
import MGAP4D.R6.Theorem.IntervalSkeleton

namespace MGAP4D
namespace R6
namespace Theorem

structure IntervalExclusionProofObligationTighteningPass1 where
  segmentSelectionGreen : Prop
  theoremSkeletonVisible : Prop
  r5BridgeObligationSeparated : Prop
  vacuumSideObligationSeparated : Prop
  excitedSideObligationSeparated : Prop
  intervalBoundaryObligationSeparated : Prop
  intervalExclusionTargetObligationSeparated : Prop
  mathlibRequestBoundarySeparated : Prop
  statusCompatibilityBoundarySeparated : Prop
  upstreamR5ReviewDependencySeparated : Prop
  downstreamR7ReviewGateSeparated : Prop
  publicBoundaryObligationSeparated : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  theoremCompletionNotClaimed : Prop
  downstreamR7NotUnlocked : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def IntervalExclusionProofObligationTighteningPass1.ready
    (P : IntervalExclusionProofObligationTighteningPass1) : Prop :=
  P.segmentSelectionGreen ∧ P.theoremSkeletonVisible ∧
  P.r5BridgeObligationSeparated ∧ P.vacuumSideObligationSeparated ∧
  P.excitedSideObligationSeparated ∧ P.intervalBoundaryObligationSeparated ∧
  P.intervalExclusionTargetObligationSeparated ∧ P.mathlibRequestBoundarySeparated ∧
  P.statusCompatibilityBoundarySeparated ∧ P.upstreamR5ReviewDependencySeparated ∧
  P.downstreamR7ReviewGateSeparated ∧ P.publicBoundaryObligationSeparated ∧
  P.mainPreMathlib ∧ P.mathlibMainAdoptionHeld ∧ P.theoremCompletionNotClaimed ∧
  P.downstreamR7NotUnlocked ∧ P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld

theorem interval_exclusion_proof_obligation_tightening_pass1_pack
    (P : IntervalExclusionProofObligationTighteningPass1) :
    P.ready ↔ P.segmentSelectionGreen ∧ P.theoremSkeletonVisible ∧
      P.r5BridgeObligationSeparated ∧ P.vacuumSideObligationSeparated ∧
      P.excitedSideObligationSeparated ∧ P.intervalBoundaryObligationSeparated ∧
      P.intervalExclusionTargetObligationSeparated ∧ P.mathlibRequestBoundarySeparated ∧
      P.statusCompatibilityBoundarySeparated ∧ P.upstreamR5ReviewDependencySeparated ∧
      P.downstreamR7ReviewGateSeparated ∧ P.publicBoundaryObligationSeparated ∧
      P.mainPreMathlib ∧ P.mathlibMainAdoptionHeld ∧ P.theoremCompletionNotClaimed ∧
      P.downstreamR7NotUnlocked ∧ P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld := by
  rfl

end Theorem
end R6
end MGAP4D
