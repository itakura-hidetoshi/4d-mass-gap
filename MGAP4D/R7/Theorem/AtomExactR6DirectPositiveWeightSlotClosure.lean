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
final global theorem release. -/
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

/-- Build the R7 proof-obligation tightening closure with the atom-persistence,
exact-gap, and upstream-R6 review slots supplied by the R6 direct
positive-weight bridge.

All other review gates remain explicit parameters, so this is a local closure of
R7's direct positive-weight slot rather than a final theorem release. -/
theorem atom_exact_tightening_closure_ready_of_r6_direct_positive_weight_slot
    {pass1Green pass2Green pass3Green seriesReviewGreen tighteningSegmentClosed
      eigenstateSurfaceClosedAtReviewSurface globalExportClosedAtReviewSurface
      reviewGateClosedAtReviewSurface mathlibRequestBoundaryClosedAtReviewSurface
      statusCompatibilityBoundaryClosedAtReviewSurface finalAssemblyReviewSurfaceClosed
      publicBoundaryClosedAtReviewSurface threeLayerLinksClosedAtReviewSurface
      r7TheoremRouteStillOpen mainPreMathlib mathlibMainAdoptionHeld
      theoremCompletionNotClaimed finalGapReleaseNotUnlocked publicBoundaryHeld : Prop}
    (hpass1 : pass1Green)
    (hpass2 : pass2Green)
    (hpass3 : pass3Green)
    (hseries : seriesReviewGreen)
    (htightening : tighteningSegmentClosed)
    (heigenstate : eigenstateSurfaceClosedAtReviewSurface)
    (hglobalExport : globalExportClosedAtReviewSurface)
    (hreviewGate : reviewGateClosedAtReviewSurface)
    (hmathlibRequest : mathlibRequestBoundaryClosedAtReviewSurface)
    (hstatus : statusCompatibilityBoundaryClosedAtReviewSurface)
    (hfinalAssembly : finalAssemblyReviewSurfaceClosed)
    (hpublicReview : publicBoundaryClosedAtReviewSurface)
    (hthreeLayer : threeLayerLinksClosedAtReviewSurface)
    (hr7Open : r7TheoremRouteStillOpen)
    (hpreMathlib : mainPreMathlib)
    (hmathlibHeld : mathlibMainAdoptionHeld)
    (hnotComplete : theoremCompletionNotClaimed)
    (hfinalLocked : finalGapReleaseNotUnlocked)
    (hpublic : publicBoundaryHeld) :
    (AtomExactProofObligationTighteningClosure.mk
      pass1Green
      pass2Green
      pass3Green
      seriesReviewGreen
      tighteningSegmentClosed
      AtomExactR6DirectPositiveWeightReviewSurfaceClosed
      eigenstateSurfaceClosedAtReviewSurface
      AtomExactR6DirectPositiveWeightReviewSurfaceClosed
      globalExportClosedAtReviewSurface
      reviewGateClosedAtReviewSurface
      mathlibRequestBoundaryClosedAtReviewSurface
      statusCompatibilityBoundaryClosedAtReviewSurface
      AtomExactR6DirectPositiveWeightReviewSurfaceClosed
      finalAssemblyReviewSurfaceClosed
      publicBoundaryClosedAtReviewSurface
      threeLayerLinksClosedAtReviewSurface
      r7TheoremRouteStillOpen
      mainPreMathlib
      mathlibMainAdoptionHeld
      theoremCompletionNotClaimed
      finalGapReleaseNotUnlocked
      publicBoundaryHeld).ready := by
  exact ⟨
    hpass1,
    hpass2,
    hpass3,
    hseries,
    htightening,
    atom_exact_r6_direct_positive_weight_review_surface_closed,
    heigenstate,
    atom_exact_r6_direct_positive_weight_review_surface_closed,
    hglobalExport,
    hreviewGate,
    hmathlibRequest,
    hstatus,
    atom_exact_r6_direct_positive_weight_review_surface_closed,
    hfinalAssembly,
    hpublicReview,
    hthreeLayer,
    hr7Open,
    hpreMathlib,
    hmathlibHeld,
    hnotComplete,
    hfinalLocked,
    hpublic⟩

/-- One-line export: the R7 atom-exact positive-weight review slot is now closed
by the R6 direct exact-atom bridge. -/
theorem r7_atom_exact_r6_direct_positive_weight_slot_ready :
    AtomExactR6DirectPositiveWeightReviewSurfaceClosed := by
  exact atom_exact_r6_direct_positive_weight_review_surface_closed

end

end Theorem
end R7
end MGAP4D
