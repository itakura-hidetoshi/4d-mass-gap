import MGAP4D.R4.Theorem.LowerBoundTighteningSegmentSelection
import MGAP4D.R4.Theorem.LowerBoundSkeleton

namespace MGAP4D
namespace R4
namespace Theorem

structure LowerBoundProofObligationTighteningPass1 where
  segmentSelectionGreen : Prop
  theoremSkeletonVisible : Prop
  lowerBoundCoreObligationSeparated : Prop
  constantNormalizationObligationSeparated : Prop
  ledgerTraceObligationSeparated : Prop
  operatorBridgeObligationSeparated : Prop
  estimateObligationSeparated : Prop
  upstreamR3ReviewDependencySeparated : Prop
  upstreamR2BridgeDependencySeparated : Prop
  downstreamR5R7ReviewGateSeparated : Prop
  publicBoundaryObligationSeparated : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  theoremCompletionNotClaimed : Prop
  downstreamR5R7NotUnlocked : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def LowerBoundProofObligationTighteningPass1.ready
    (P : LowerBoundProofObligationTighteningPass1) : Prop :=
  P.segmentSelectionGreen ∧ P.theoremSkeletonVisible ∧
  P.lowerBoundCoreObligationSeparated ∧ P.constantNormalizationObligationSeparated ∧
  P.ledgerTraceObligationSeparated ∧ P.operatorBridgeObligationSeparated ∧
  P.estimateObligationSeparated ∧ P.upstreamR3ReviewDependencySeparated ∧
  P.upstreamR2BridgeDependencySeparated ∧ P.downstreamR5R7ReviewGateSeparated ∧
  P.publicBoundaryObligationSeparated ∧ P.mainPreMathlib ∧
  P.mathlibMainAdoptionHeld ∧ P.theoremCompletionNotClaimed ∧
  P.downstreamR5R7NotUnlocked ∧ P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld

theorem lower_bound_proof_obligation_tightening_pass1_pack
    (P : LowerBoundProofObligationTighteningPass1) :
    P.ready ↔ P.segmentSelectionGreen ∧ P.theoremSkeletonVisible ∧
      P.lowerBoundCoreObligationSeparated ∧ P.constantNormalizationObligationSeparated ∧
      P.ledgerTraceObligationSeparated ∧ P.operatorBridgeObligationSeparated ∧
      P.estimateObligationSeparated ∧ P.upstreamR3ReviewDependencySeparated ∧
      P.upstreamR2BridgeDependencySeparated ∧ P.downstreamR5R7ReviewGateSeparated ∧
      P.publicBoundaryObligationSeparated ∧ P.mainPreMathlib ∧
      P.mathlibMainAdoptionHeld ∧ P.theoremCompletionNotClaimed ∧
      P.downstreamR5R7NotUnlocked ∧ P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld := by
  rfl

end Theorem
end R4
end MGAP4D
