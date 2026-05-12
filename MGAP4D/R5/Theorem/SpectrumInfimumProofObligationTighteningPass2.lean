import MGAP4D.R5.Concrete.SpectrumTheoremChecklist
import MGAP4D.R5.Concrete.SpectrumProofObligationMap
import MGAP4D.R5.Theorem.SpectrumSkeleton
import MGAP4D.R5.Theorem.SpectrumInfimumProofObligationTighteningPass1

namespace MGAP4D
namespace R5
namespace Theorem

structure SpectrumInfimumProofObligationTighteningPass2 where
  pass1Visible : Prop
  checklistLayerVisible : Prop
  obligationMapLayerVisible : Prop
  theoremSkeletonLayerVisible : Prop
  spectrumSetChecklistToMapToSkeleton : Prop
  spectrumBottomChecklistToMapToSkeleton : Prop
  witnessChecklistToMapToSkeleton : Prop
  comparisonChecklistToMapToSkeleton : Prop
  infimumChecklistToMapToSkeleton : Prop
  upstreamR4LowerBoundSurfaceToSkeleton : Prop
  upstreamR3ZeroFormSurfaceToSkeleton : Prop
  downstreamR6R7GateSurfaceToSkeleton : Prop
  mathlibRequestChecklistToMapToSkeleton : Prop
  publicBoundaryChecklistToMapToSkeleton : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  theoremCompletionNotClaimed : Prop
  downstreamR6R7NotUnlocked : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def SpectrumInfimumProofObligationTighteningPass2.ready
    (P : SpectrumInfimumProofObligationTighteningPass2) : Prop :=
  P.pass1Visible ∧ P.checklistLayerVisible ∧ P.obligationMapLayerVisible ∧
  P.theoremSkeletonLayerVisible ∧ P.spectrumSetChecklistToMapToSkeleton ∧
  P.spectrumBottomChecklistToMapToSkeleton ∧ P.witnessChecklistToMapToSkeleton ∧
  P.comparisonChecklistToMapToSkeleton ∧ P.infimumChecklistToMapToSkeleton ∧
  P.upstreamR4LowerBoundSurfaceToSkeleton ∧ P.upstreamR3ZeroFormSurfaceToSkeleton ∧
  P.downstreamR6R7GateSurfaceToSkeleton ∧ P.mathlibRequestChecklistToMapToSkeleton ∧
  P.publicBoundaryChecklistToMapToSkeleton ∧ P.mainPreMathlib ∧
  P.mathlibMainAdoptionHeld ∧ P.theoremCompletionNotClaimed ∧
  P.downstreamR6R7NotUnlocked ∧ P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld

theorem spectrum_infimum_proof_obligation_tightening_pass2_pack
    (P : SpectrumInfimumProofObligationTighteningPass2) :
    P.ready ↔ P.pass1Visible ∧ P.checklistLayerVisible ∧ P.obligationMapLayerVisible ∧
      P.theoremSkeletonLayerVisible ∧ P.spectrumSetChecklistToMapToSkeleton ∧
      P.spectrumBottomChecklistToMapToSkeleton ∧ P.witnessChecklistToMapToSkeleton ∧
      P.comparisonChecklistToMapToSkeleton ∧ P.infimumChecklistToMapToSkeleton ∧
      P.upstreamR4LowerBoundSurfaceToSkeleton ∧ P.upstreamR3ZeroFormSurfaceToSkeleton ∧
      P.downstreamR6R7GateSurfaceToSkeleton ∧ P.mathlibRequestChecklistToMapToSkeleton ∧
      P.publicBoundaryChecklistToMapToSkeleton ∧ P.mainPreMathlib ∧
      P.mathlibMainAdoptionHeld ∧ P.theoremCompletionNotClaimed ∧
      P.downstreamR6R7NotUnlocked ∧ P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld := by
  rfl

end Theorem
end R5
end MGAP4D
