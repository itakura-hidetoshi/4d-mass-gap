import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedMergeOrderCorrection
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Ordered public surface for the complete Yang--Mills direct bounded construction.

This file promotes the post-merge-order-correction state to a theorem-facing
ordered public surface.  The complete-construction handoff layer and the root
public API layer are packaged together, with explicit Lean proofs that both
project to the same direct bounded public markers.

It does not add a spectral theorem invocation, spectral projection construction,
functional-calculus layer, numerical gap bound, or final Yang--Mills mass-gap
claim.
-/

/-- Ordered public surface joining the complete-construction handoff layer and
the root public API layer after the #722/#723 merge-order correction. -/
structure EuclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) where
  handoff : EuclideanYangMillsCompleteConstructionDirectBoundedPublicHandoff S
  rootPublicCertificate : EuclideanYangMillsCompleteConstructionDirectBoundedCertificate S
  status_agrees : rootPublicCertificate.publicHandoffStatus = handoff.publicHandoffStatus
  endpointNames_agrees : rootPublicCertificate.directEndpointNames = handoff.directEndpointNames
  primaryRoute_eq :
    _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
      "bare-M-direct-bundle"
  compatibilityRole_eq :
    _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
      "compatibility-only"

/-- Canonical ordered public surface for the complete Yang--Mills direct bounded
construction. -/
def euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface S :=
  { handoff := euclideanYangMillsCompleteConstructionDirectBoundedPublicHandoff S
    rootPublicCertificate :=
      euclideanYangMillsCompleteConstructionDirectBoundedRootPublicCertificate S
    status_agrees :=
      euclideanYangMillsCompleteConstructionDirectBoundedMergeOrderStatus_agrees S
    endpointNames_agrees :=
      euclideanYangMillsCompleteConstructionDirectBoundedMergeOrderEndpointNames_agrees S
    primaryRoute_eq :=
      euclideanYangMillsCompleteConstructionDirectBoundedRootPublicPrimaryRoute S
    compatibilityRole_eq :=
      euclideanYangMillsCompleteConstructionDirectBoundedRootPublicCompatibilityRole S }

/-- The ordered public surface has the canonical direct bounded status marker on
both joined surfaces. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface_status
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (O : EuclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface S) :
    O.rootPublicCertificate.publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" ∧
      O.handoff.publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" := by
  have hroot : O.rootPublicCertificate.publicHandoffStatus = O.handoff.publicHandoffStatus :=
    O.status_agrees
  have hhandoff :
      O.handoff.publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" := by
    rw [O.handoff.publicHandoffStatus_eq]
    exact
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_direct_bounded_public_handoff_status_eq
  exact ⟨hroot.trans hhandoff, hhandoff⟩

/-- The ordered public surface has the canonical direct endpoint-name list on
both joined surfaces. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface_endpointNames
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (O : EuclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface S) :
    O.rootPublicCertificate.directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] ∧
      O.handoff.directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] := by
  have hroot : O.rootPublicCertificate.directEndpointNames = O.handoff.directEndpointNames :=
    O.endpointNames_agrees
  have hhandoff :
      O.handoff.directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] := by
    rw [O.handoff.directEndpointNames_eq]
    exact
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_direct_bounded_public_endpoint_names_eq
  exact ⟨hroot.trans hhandoff, hhandoff⟩

/-- Canonical ordered route-marker package for downstream imports. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface_routeMarkers
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface S).rootPublicCertificate.publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" ∧
      (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface S).handoff.publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
        "bare-M-direct-bundle" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
        "compatibility-only" := by
  let O := euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface S
  exact ⟨
    (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface_status S O).1,
    (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface_status S O).2,
    O.primaryRoute_eq,
    O.compatibilityRole_eq⟩

/-- Canonical ordered endpoint-name package for downstream imports. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface_endpointPackage
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface S).rootPublicCertificate.directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] ∧
      (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface S).handoff.directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] := by
  exact
    euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface_endpointNames S
      (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface S)

end

end MathlibAnalytic
end MGAP4D
