import MGAP4D.R2.Concrete.RestrictionTheoremChecklist
import MGAP4D.R2.Concrete.RestrictionProofObligationMap
import MGAP4D.R2.Theorem.RestrictionSkeleton
import MGAP4D.R2.Theorem.RestrictionProofObligationTighteningPass1

namespace MGAP4D
namespace R2
namespace Theorem

structure RestrictionProofObligationTighteningPass2 where
  pass1Visible : Prop
  checklistLayerVisible : Prop
  obligationMapLayerVisible : Prop
  theoremSkeletonLayerVisible : Prop
  reducingSubspaceChecklistToMapToSkeleton : Prop
  fullHamiltonianSelfAdjointChecklistToMapToSkeleton : Prop
  restrictionDomainChecklistToMapToSkeleton : Prop
  restrictionOperatorChecklistToMapToSkeleton : Prop
  restrictionSelfAdjointChecklistToMapToSkeleton : Prop
  operatorAPIBridgeChecklistToMapToSkeleton : Prop
  mathlibRequestChecklistToMapToSkeleton : Prop
  statusCompatibilityChecklistToMapToSkeleton : Prop
  publicBoundaryChecklistToMapToSkeleton : Prop
  r1ClosurePreserved : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  r2TheoremCompletionNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def RestrictionProofObligationTighteningPass2.ready
    (P : RestrictionProofObligationTighteningPass2) : Prop :=
  P.pass1Visible ∧ P.checklistLayerVisible ∧ P.obligationMapLayerVisible ∧
  P.theoremSkeletonLayerVisible ∧ P.reducingSubspaceChecklistToMapToSkeleton ∧
  P.fullHamiltonianSelfAdjointChecklistToMapToSkeleton ∧
  P.restrictionDomainChecklistToMapToSkeleton ∧ P.restrictionOperatorChecklistToMapToSkeleton ∧
  P.restrictionSelfAdjointChecklistToMapToSkeleton ∧ P.operatorAPIBridgeChecklistToMapToSkeleton ∧
  P.mathlibRequestChecklistToMapToSkeleton ∧ P.statusCompatibilityChecklistToMapToSkeleton ∧
  P.publicBoundaryChecklistToMapToSkeleton ∧ P.r1ClosurePreserved ∧
  P.mainPreMathlib ∧ P.mathlibMainAdoptionHeld ∧ P.r2TheoremCompletionNotClaimed ∧
  P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld

theorem restriction_proof_obligation_tightening_pass2_pack
    (P : RestrictionProofObligationTighteningPass2) :
    P.ready ↔ P.pass1Visible ∧ P.checklistLayerVisible ∧ P.obligationMapLayerVisible ∧
      P.theoremSkeletonLayerVisible ∧ P.reducingSubspaceChecklistToMapToSkeleton ∧
      P.fullHamiltonianSelfAdjointChecklistToMapToSkeleton ∧
      P.restrictionDomainChecklistToMapToSkeleton ∧ P.restrictionOperatorChecklistToMapToSkeleton ∧
      P.restrictionSelfAdjointChecklistToMapToSkeleton ∧ P.operatorAPIBridgeChecklistToMapToSkeleton ∧
      P.mathlibRequestChecklistToMapToSkeleton ∧ P.statusCompatibilityChecklistToMapToSkeleton ∧
      P.publicBoundaryChecklistToMapToSkeleton ∧ P.r1ClosurePreserved ∧
      P.mainPreMathlib ∧ P.mathlibMainAdoptionHeld ∧ P.r2TheoremCompletionNotClaimed ∧
      P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld := by
  rfl

end Theorem
end R2
end MGAP4D
