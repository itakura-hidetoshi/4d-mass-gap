import MGAP4D.R7.Theorem.AtomExactR6DirectPositiveWeightBridge
import MGAP4D.R7.Theorem.AtomExactProofObligationTighteningClosure

namespace MGAP4D
namespace R7
namespace Theorem

open scoped BigOperators ENNReal lp

noncomputable section

/-- R7 review-surface closure supplied by the R6 direct exact-atom bridge and the
positive plaquette spectral-weight certificate.

This closes a review slot only: it records positive mass, exact real atom value,
atom membership, and non-vacuum orthogonal-sector placement.  It does not unlock
final global release. -/
def AtomExactR6DirectPositiveWeightReviewSurfaceClosed : Prop :=
  AtomExactR6DirectPositiveWeightBridgeReady ∧
  MGAP4D.Plaquette.observableSpectralWeight3320Certificate.massWitness.positiveMass = true ∧
  MGAP4D.MathlibAnalytic.exactGapValueReal = (33 : ℝ) / 20 ∧
  MGAP4D.MathlibAnalytic.exactGapValueReal ∈
    MGAP4D.MathlibAnalytic.singletonObservableAtomTheoremTheoremData.atom ∧
  MGAP4D.Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector =
    MGAP4D.Spectral.SpectralSector.orthogonal ∧
  MGAP4D.Plaquette.observableSpectralWeight3320Certificate.sectorSeparation.witnessSector ≠
    MGAP4D.Spectral.SpectralSector.vacuum

/-- The R7 R6-positive-weight review surface is closed by the direct bridge. -/
theorem atom_exact_r6_direct_positive_weight_review_surface_closed :
    AtomExactR6DirectPositiveWeightReviewSurfaceClosed := by
  exact ⟨
    atom_exact_r6_direct_positive_weight_bridge_ready,
    atom_exact_r6_direct_positive_weight_bridge_positive_mass,
    atom_exact_r6_direct_positive_weight_bridge_real_value_eq,
    atom_exact_r6_direct_positive_weight_bridge_real_value_mem_atom,
    atom_exact_r6_direct_positive_weight_bridge_orthogonal_nonvacuum.1,
    atom_exact_r6_direct_positive_weight_bridge_orthogonal_nonvacuum.2⟩

/-- Build an R7 closure-candidate readiness package whose upstream R6 interval
slot is supplied by the direct R6 exact-atom/positive-weight review bridge. -/
theorem atom_exact_closure_candidate_ready_of_r6_direct_positive_weight_slot
    {milestonePresent skeletonBundlePresent atomSurfaceNamed exactGapSurfaceNamed
      finalValueBoundaryReviewGated atomExactObligationsVisible
      upstreamR5SpectrumInfimumVisible mathlibDryRunNotCompletion publicBoundaryHeld : Prop}
    (hmilestone : milestonePresent)
    (hskeleton : skeletonBundlePresent)
    (hatomSurface : atomSurfaceNamed)
    (hexactSurface : exactGapSurfaceNamed)
    (hfinalValueBoundary : finalValueBoundaryReviewGated)
    (hobligations : atomExactObligationsVisible)
    (hupstreamR5 : upstreamR5SpectrumInfimumVisible)
    (hmathlib : mathlibDryRunNotCompletion)
    (hpublic : publicBoundaryHeld) :
    (AtomExactClosureCandidate.mk
      milestonePresent
      skeletonBundlePresent
      atomSurfaceNamed
      exactGapSurfaceNamed
      finalValueBoundaryReviewGated
      atomExactObligationsVisible
      upstreamR5SpectrumInfimumVisible
      AtomExactR6DirectPositiveWeightReviewSurfaceClosed
      mathlibDryRunNotCompletion
      publicBoundaryHeld).ready := by
  exact ⟨
    hmilestone,
    hskeleton,
    hatomSurface,
    hexactSurface,
    hfinalValueBoundary,
    hobligations,
    hupstreamR5,
    atom_exact_r6_direct_positive_weight_review_surface_closed,
    hmathlib,
    hpublic⟩

/-- Build an R7 hardening-pass readiness package whose upstream R6 interval slot
is supplied by the direct R6 exact-atom/positive-weight review bridge. -/
theorem atom_exact_hardening_pass_ready_of_r6_direct_positive_weight_slot
    {closureCandidateVisible atomSurfaceVisible exactGapSurfaceVisible
      finalValueBoundaryReviewGated atomExactObligationsVisible
      upstreamR5SpectrumInfimumVisible mathlibDryRunNotCompletion
      theoremCompletionNotClaimed finalGapReleaseNotUnlocked publicBoundaryHeld : Prop}
    (hclosure : closureCandidateVisible)
    (hatomSurface : atomSurfaceVisible)
    (hexactSurface : exactGapSurfaceVisible)
    (hfinalValueBoundary : finalValueBoundaryReviewGated)
    (hobligations : atomExactObligationsVisible)
    (hupstreamR5 : upstreamR5SpectrumInfimumVisible)
    (hmathlib : mathlibDryRunNotCompletion)
    (hnotComplete : theoremCompletionNotClaimed)
    (hfinalLocked : finalGapReleaseNotUnlocked)
    (hpublic : publicBoundaryHeld) :
    (AtomExactHardeningPass.mk
      closureCandidateVisible
      atomSurfaceVisible
      exactGapSurfaceVisible
      finalValueBoundaryReviewGated
      atomExactObligationsVisible
      upstreamR5SpectrumInfimumVisible
      AtomExactR6DirectPositiveWeightReviewSurfaceClosed
      mathlibDryRunNotCompletion
      theoremCompletionNotClaimed
      finalGapReleaseNotUnlocked
      publicBoundaryHeld).ready := by
  exact ⟨
    hclosure,
    hatomSurface,
    hexactSurface,
    hfinalValueBoundary,
    hobligations,
    hupstreamR5,
    atom_exact_r6_direct_positive_weight_review_surface_closed,
    hmathlib,
    hnotComplete,
    hfinalLocked,
    hpublic⟩

/-- Input bundle for the local R7 tightening closure.  The R6 direct positive
weight bridge fills the atom-persistence, exact-gap, and upstream-R6 slots; the
remaining gates stay explicit in this bundle. -/
structure AtomExactR6DirectPositiveWeightClosureInputs where
  pass1Green : Prop
  pass2Green : Prop
  pass3Green : Prop
  seriesReviewGreen : Prop
  tighteningSegmentClosed : Prop
  eigenstateSurfaceClosedAtReviewSurface : Prop
  globalExportClosedAtReviewSurface : Prop
  reviewGateClosedAtReviewSurface : Prop
  mathlibRequestBoundaryClosedAtReviewSurface : Prop
  statusCompatibilityBoundaryClosedAtReviewSurface : Prop
  finalAssemblyReviewSurfaceClosed : Prop
  publicBoundaryClosedAtReviewSurface : Prop
  threeLayerLinksClosedAtReviewSurface : Prop
  r7TheoremRouteStillOpen : Prop
  mainPreMathlib : Prop
  mathlibMainAdoptionHeld : Prop
  theoremCompletionNotClaimed : Prop
  finalGapReleaseNotUnlocked : Prop
  publicBoundaryHeld : Prop
  hpass1 : pass1Green
  hpass2 : pass2Green
  hpass3 : pass3Green
  hseries : seriesReviewGreen
  htightening : tighteningSegmentClosed
  heigenstate : eigenstateSurfaceClosedAtReviewSurface
  hglobalExport : globalExportClosedAtReviewSurface
  hreviewGate : reviewGateClosedAtReviewSurface
  hmathlibRequest : mathlibRequestBoundaryClosedAtReviewSurface
  hstatus : statusCompatibilityBoundaryClosedAtReviewSurface
  hfinalAssembly : finalAssemblyReviewSurfaceClosed
  hpublicReview : publicBoundaryClosedAtReviewSurface
  hthreeLayer : threeLayerLinksClosedAtReviewSurface
  hr7Open : r7TheoremRouteStillOpen
  hpreMathlib : mainPreMathlib
  hmathlibHeld : mathlibMainAdoptionHeld
  hnotComplete : theoremCompletionNotClaimed
  hfinalLocked : finalGapReleaseNotUnlocked
  hpublic : publicBoundaryHeld

/-- Package the R7 tightening closure with the local positive-weight review
surface inserted into the three slots it actually closes. -/
def atomExactR6DirectPositiveWeightTighteningClosurePackage
    (I : AtomExactR6DirectPositiveWeightClosureInputs) :
    AtomExactProofObligationTighteningClosure :=
  { pass1Green := I.pass1Green
    pass2Green := I.pass2Green
    pass3Green := I.pass3Green
    seriesReviewGreen := I.seriesReviewGreen
    tighteningSegmentClosed := I.tighteningSegmentClosed
    atomPersistenceClosedAtReviewSurface := AtomExactR6DirectPositiveWeightReviewSurfaceClosed
    eigenstateSurfaceClosedAtReviewSurface := I.eigenstateSurfaceClosedAtReviewSurface
    exactGapValueClosedAtReviewSurface := AtomExactR6DirectPositiveWeightReviewSurfaceClosed
    globalExportClosedAtReviewSurface := I.globalExportClosedAtReviewSurface
    reviewGateClosedAtReviewSurface := I.reviewGateClosedAtReviewSurface
    mathlibRequestBoundaryClosedAtReviewSurface := I.mathlibRequestBoundaryClosedAtReviewSurface
    statusCompatibilityBoundaryClosedAtReviewSurface := I.statusCompatibilityBoundaryClosedAtReviewSurface
    upstreamR6ReviewSurfaceClosed := AtomExactR6DirectPositiveWeightReviewSurfaceClosed
    finalAssemblyReviewSurfaceClosed := I.finalAssemblyReviewSurfaceClosed
    publicBoundaryClosedAtReviewSurface := I.publicBoundaryClosedAtReviewSurface
    threeLayerLinksClosedAtReviewSurface := I.threeLayerLinksClosedAtReviewSurface
    r7TheoremRouteStillOpen := I.r7TheoremRouteStillOpen
    mainPreMathlib := I.mainPreMathlib
    mathlibMainAdoptionHeld := I.mathlibMainAdoptionHeld
    theoremCompletionNotClaimed := I.theoremCompletionNotClaimed
    finalGapReleaseNotUnlocked := I.finalGapReleaseNotUnlocked
    publicBoundaryHeld := I.publicBoundaryHeld }

/-- The local R7 tightening package is ready whenever its still-explicit gates are
witnessed. -/
theorem atom_exact_tightening_closure_ready_of_r6_direct_positive_weight_slot
    (I : AtomExactR6DirectPositiveWeightClosureInputs) :
    (atomExactR6DirectPositiveWeightTighteningClosurePackage I).ready := by
  exact ⟨
    I.hpass1,
    I.hpass2,
    I.hpass3,
    I.hseries,
    I.htightening,
    atom_exact_r6_direct_positive_weight_review_surface_closed,
    I.heigenstate,
    atom_exact_r6_direct_positive_weight_review_surface_closed,
    I.hglobalExport,
    I.hreviewGate,
    I.hmathlibRequest,
    I.hstatus,
    atom_exact_r6_direct_positive_weight_review_surface_closed,
    I.hfinalAssembly,
    I.hpublicReview,
    I.hthreeLayer,
    I.hr7Open,
    I.hpreMathlib,
    I.hmathlibHeld,
    I.hnotComplete,
    I.hfinalLocked,
    I.hpublic⟩

/-- One-line export: the R7 atom-exact positive-weight review slot is now closed
by the R6 direct exact-atom bridge. -/
theorem r7_atom_exact_r6_direct_positive_weight_slot_ready :
    AtomExactR6DirectPositiveWeightReviewSurfaceClosed := by
  exact atom_exact_r6_direct_positive_weight_review_surface_closed

end

end Theorem
end R7
end MGAP4D
