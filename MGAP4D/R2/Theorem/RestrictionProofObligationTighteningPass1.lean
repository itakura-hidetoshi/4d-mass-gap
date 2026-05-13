import MGAP4D.R2.Theorem.RestrictionTighteningSegmentSelection
import MGAP4D.R2.Theorem.RestrictionSkeleton

namespace MGAP4D
namespace R2
namespace Theorem

structure RestrictionProofObligationTighteningPass1 where
  segmentSelectionGreen : Prop
  theoremSkeletonVisible : Prop
  reducingSubspaceObligationSeparated : Prop
  fullHamiltonianSelfAdjointTargetObligationSeparated : Prop
  restrictionDomainObligationSeparated : Prop
  restrictionOperatorObligationSeparated : Prop
  restrictionSelfAdjointTargetObligationSeparated : Prop
  operatorAPIBridgeObligationSeparated : Prop
  mathlibRequestBoundarySeparated : Prop
  statusCompatibilityBoundarySeparated : Prop
  publicBoundaryObligationSeparated : Prop
  r1ClosurePreserved : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  r2TheoremCompletionNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def RestrictionProofObligationTighteningPass1.ready
    (P : RestrictionProofObligationTighteningPass1) : Prop :=
  P.segmentSelectionGreen ∧ P.theoremSkeletonVisible ∧
  P.reducingSubspaceObligationSeparated ∧
  P.fullHamiltonianSelfAdjointTargetObligationSeparated ∧
  P.restrictionDomainObligationSeparated ∧
  P.restrictionOperatorObligationSeparated ∧
  P.restrictionSelfAdjointTargetObligationSeparated ∧
  P.operatorAPIBridgeObligationSeparated ∧
  P.mathlibRequestBoundarySeparated ∧ P.statusCompatibilityBoundarySeparated ∧
  P.publicBoundaryObligationSeparated ∧ P.r1ClosurePreserved ∧
  P.mainPreMathlib ∧ P.mathlibMainAdoptionHeld ∧ P.r2TheoremCompletionNotClaimed ∧
  P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld

theorem restriction_proof_obligation_tightening_pass1_pack
    (P : RestrictionProofObligationTighteningPass1) :
    P.ready ↔ P.segmentSelectionGreen ∧ P.theoremSkeletonVisible ∧
      P.reducingSubspaceObligationSeparated ∧
      P.fullHamiltonianSelfAdjointTargetObligationSeparated ∧
      P.restrictionDomainObligationSeparated ∧ P.restrictionOperatorObligationSeparated ∧
      P.restrictionSelfAdjointTargetObligationSeparated ∧
      P.operatorAPIBridgeObligationSeparated ∧ P.mathlibRequestBoundarySeparated ∧
      P.statusCompatibilityBoundarySeparated ∧ P.publicBoundaryObligationSeparated ∧
      P.r1ClosurePreserved ∧ P.mainPreMathlib ∧ P.mathlibMainAdoptionHeld ∧
      P.r2TheoremCompletionNotClaimed ∧ P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld := by
  rfl

end Theorem
end R2
end MGAP4D
