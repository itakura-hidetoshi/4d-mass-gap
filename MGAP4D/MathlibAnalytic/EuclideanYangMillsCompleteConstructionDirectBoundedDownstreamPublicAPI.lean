import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Stable downstream public API for the complete Yang--Mills direct bounded route.

This file is a small import leaf above the downstream surface.  Downstream files
can import this file to access the canonical direct bounded downstream package,
status links, endpoint links, route markers, and endpoint-name package without
importing the aggregate `MGAP4D.MathlibAnalytic` root.

It does not add a spectral theorem invocation, spectral projection construction,
functional-calculus layer, numerical gap bound, or final Yang--Mills mass-gap
claim.
-/

/-- Canonical downstream public API package. -/
def euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S :=
  euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S

/-- Public API projection for the status-link package. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI_statusLinks
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI S).rootBundle.certificate.publicHandoffStatus =
        (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI S).orderedSurface.rootPublicCertificate.publicHandoffStatus ∧
      (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI S).orderedSurface.rootPublicCertificate.publicHandoffStatus =
        (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI S).handoff.publicHandoffStatus := by
  exact euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface_statusLinks S

/-- Public API projection for the endpoint-link package. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI_endpointLinks
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI S).rootBundle.certificate.directEndpointNames =
        (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI S).orderedSurface.rootPublicCertificate.directEndpointNames ∧
      (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI S).orderedSurface.rootPublicCertificate.directEndpointNames =
        (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI S).handoff.directEndpointNames := by
  exact euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface_endpointLinks S

/-- Public API projection for the canonical direct bounded route markers. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI_routeMarkers
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI S).rootBundle.certificate.publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" ∧
      (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI S).orderedSurface.rootPublicCertificate.publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" ∧
      (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI S).handoff.publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
        "bare-M-direct-bundle" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
        "compatibility-only" := by
  exact euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface_routeMarkers S

/-- Public API projection for the canonical direct bounded endpoint-name package. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI_endpointPackage
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI S).rootBundle.certificate.directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] ∧
      (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI S).orderedSurface.rootPublicCertificate.directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] ∧
      (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI S).handoff.directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] := by
  exact euclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface_endpointPackage S

/-- Combined public API endpoint for downstream imports. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI_completePackage
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI S).rootBundle.certificate.publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" ∧
      (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI S).rootBundle.certificate.directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
        "bare-M-direct-bundle" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
        "compatibility-only" := by
  exact ⟨
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI_routeMarkers S).1,
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI_endpointPackage S).1,
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI_routeMarkers S).2.2.2.1,
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI_routeMarkers S).2.2.2.2⟩

end

end MathlibAnalytic
end MGAP4D
