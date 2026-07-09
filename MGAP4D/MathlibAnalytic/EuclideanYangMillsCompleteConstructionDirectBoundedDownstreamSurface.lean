import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedBundleOrderedBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Downstream public surface for the complete Yang--Mills direct bounded route.

This file collects the complete-construction handoff, root public API bundle, and
ordered public surface into a single downstream-facing theorem package.  It is a
thin bridge layer over the already-merged direct bounded surfaces and does not
import the aggregate `MGAP4D.MathlibAnalytic` root.

It does not add a spectral theorem invocation, spectral projection construction,
functional-calculus layer, numerical gap bound, or final Yang--Mills mass-gap
claim.
-/

/-- Downstream-facing package joining the public handoff, root API bundle, and
ordered public surface for the direct bounded construction route. -/
structure EuclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) where
  handoff : EuclideanYangMillsCompleteConstructionDirectBoundedPublicHandoff S
  rootBundle : EuclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle S
  orderedSurface : EuclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface S
  bundle_ordered_status_eq :
    rootBundle.certificate.publicHandoffStatus = orderedSurface.rootPublicCertificate.publicHandoffStatus
  bundle_ordered_endpointNames_eq :
    rootBundle.certificate.directEndpointNames = orderedSurface.rootPublicCertificate.directEndpointNames
  ordered_handoff_status_eq :
    orderedSurface.rootPublicCertificate.publicHandoffStatus = handoff.publicHandoffStatus
  ordered_handoff_endpointNames_eq :
    orderedSurface.rootPublicCertificate.directEndpointNames = handoff.directEndpointNames

/-- Canonical downstream-facing package for the complete construction direct
bounded route. -/
def euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S :=
  { handoff := euclideanYangMillsCompleteConstructionDirectBoundedPublicHandoff S
    rootBundle := euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle S
    orderedSurface := euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface S
    bundle_ordered_status_eq :=
      euclideanYangMillsCompleteConstructionDirectBoundedBundleOrderedBridge_status S
    bundle_ordered_endpointNames_eq :=
      euclideanYangMillsCompleteConstructionDirectBoundedBundleOrderedBridge_endpointNames S
    ordered_handoff_status_eq :=
      (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface S).status_agrees
    ordered_handoff_endpointNames_eq :=
      (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface S).endpointNames_agrees }

/-- The downstream surface connects all status-marker carriers. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface_statusLinks
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S).rootBundle.certificate.publicHandoffStatus =
        (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S).orderedSurface.rootPublicCertificate.publicHandoffStatus ∧
      (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S).orderedSurface.rootPublicCertificate.publicHandoffStatus =
        (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S).handoff.publicHandoffStatus := by
  exact ⟨
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S).bundle_ordered_status_eq,
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S).ordered_handoff_status_eq⟩

/-- The downstream surface connects all endpoint-name carriers. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface_endpointLinks
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S).rootBundle.certificate.directEndpointNames =
        (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S).orderedSurface.rootPublicCertificate.directEndpointNames ∧
      (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S).orderedSurface.rootPublicCertificate.directEndpointNames =
        (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S).handoff.directEndpointNames := by
  exact ⟨
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S).bundle_ordered_endpointNames_eq,
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S).ordered_handoff_endpointNames_eq⟩

/-- Canonical downstream route-marker package. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface_routeMarkers
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S).rootBundle.certificate.publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" ∧
      (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S).orderedSurface.rootPublicCertificate.publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" ∧
      (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S).handoff.publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
        "bare-M-direct-bundle" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
        "compatibility-only" := by
  let D := euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle_status S,
    (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface_status S D.orderedSurface).1,
    (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface_status S D.orderedSurface).2,
    euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle_primary_route S,
    euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle_compatibility_role S⟩

/-- Canonical downstream endpoint-name package. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface_endpointPackage
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S).rootBundle.certificate.directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] ∧
      (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S).orderedSurface.rootPublicCertificate.directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] ∧
      (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S).handoff.directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] := by
  let D := euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle_endpoint_names S,
    (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface_endpointNames S D.orderedSurface).1,
    (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface_endpointNames S D.orderedSurface).2⟩

end

end MathlibAnalytic
end MGAP4D
