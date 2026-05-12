import MGAP4D.R7.Theorem.AtomExactTighteningSegmentSelection
import MGAP4D.R7.Theorem.AtomExactSkeleton

namespace MGAP4D
namespace R7
namespace Theorem

structure AtomExactProofObligationTighteningPass1 where
  segmentSelectionGreen : Prop
  theoremSkeletonVisible : Prop
  atomPersistenceObligationSeparated : Prop
  eigenstateSurfaceObligationSeparated : Prop
  exactGapValueObligationSeparated : Prop
  globalExportObligationSeparated : Prop
  reviewGateObligationSeparated : Prop
  mathlibRequestBoundarySeparated : Prop
  statusCompatibilityBoundarySeparated : Prop
  upstreamR6ReviewDependencySeparated : Prop
  finalAssemblyReviewGateSeparated : Prop
  publicBoundaryObligationSeparated : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  theoremCompletionNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop

def AtomExactProofObligationTighteningPass1.ready
    (P : AtomExactProofObligationTighteningPass1) : Prop :=
  P.segmentSelectionGreen ∧ P.theoremSkeletonVisible ∧
  P.atomPersistenceObligationSeparated ∧ P.eigenstateSurfaceObligationSeparated ∧
  P.exactGapValueObligationSeparated ∧ P.globalExportObligationSeparated ∧
  P.reviewGateObligationSeparated ∧ P.mathlibRequestBoundarySeparated ∧
  P.statusCompatibilityBoundarySeparated ∧ P.upstreamR6ReviewDependencySeparated ∧
  P.finalAssemblyReviewGateSeparated ∧ P.publicBoundaryObligationSeparated ∧
  P.mainPreMathlib ∧ P.mathlibMainAdoptionHeld ∧ P.theoremCompletionNotClaimed ∧
  P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld

theorem atom_exact_proof_obligation_tightening_pass1_pack
    (P : AtomExactProofObligationTighteningPass1) :
    P.ready ↔ P.segmentSelectionGreen ∧ P.theoremSkeletonVisible ∧
      P.atomPersistenceObligationSeparated ∧ P.eigenstateSurfaceObligationSeparated ∧
      P.exactGapValueObligationSeparated ∧ P.globalExportObligationSeparated ∧
      P.reviewGateObligationSeparated ∧ P.mathlibRequestBoundarySeparated ∧
      P.statusCompatibilityBoundarySeparated ∧ P.upstreamR6ReviewDependencySeparated ∧
      P.finalAssemblyReviewGateSeparated ∧ P.publicBoundaryObligationSeparated ∧
      P.mainPreMathlib ∧ P.mathlibMainAdoptionHeld ∧ P.theoremCompletionNotClaimed ∧
      P.finalGapReleaseNotUnlocked ∧ P.publicBoundaryHeld := by
  rfl

end Theorem
end R7
end MGAP4D
