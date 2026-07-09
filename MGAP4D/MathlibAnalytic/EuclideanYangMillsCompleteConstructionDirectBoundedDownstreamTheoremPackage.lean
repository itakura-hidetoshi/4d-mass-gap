import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPISmoke
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Downstream theorem package for the complete Yang--Mills direct bounded public API.

This file turns the import smoke layer into a small theorem-facing package.  A
downstream file can import this package and obtain the canonical public API
carrier together with the status, endpoint-name, and route-marker receipts.

It does not add a spectral theorem invocation, spectral projection construction,
functional-calculus layer, numerical gap bound, or final Yang--Mills mass-gap
claim.
-/

/-- Theorem-facing package extracted from the stable downstream public API leaf. -/
structure EuclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) where
  publicAPI : EuclideanYangMillsCompleteConstructionDirectBoundedDownstreamSurface S
  statusLinks :
    publicAPI.rootBundle.certificate.publicHandoffStatus =
        publicAPI.orderedSurface.rootPublicCertificate.publicHandoffStatus ∧
      publicAPI.orderedSurface.rootPublicCertificate.publicHandoffStatus =
        publicAPI.handoff.publicHandoffStatus
  endpointLinks :
    publicAPI.rootBundle.certificate.directEndpointNames =
        publicAPI.orderedSurface.rootPublicCertificate.directEndpointNames ∧
      publicAPI.orderedSurface.rootPublicCertificate.directEndpointNames =
        publicAPI.handoff.directEndpointNames
  routeMarkers :
    publicAPI.rootBundle.certificate.publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" ∧
      publicAPI.orderedSurface.rootPublicCertificate.publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" ∧
      publicAPI.handoff.publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
        "bare-M-direct-bundle" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
        "compatibility-only"
  endpointPackage :
    publicAPI.rootBundle.certificate.directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] ∧
      publicAPI.orderedSurface.rootPublicCertificate.directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] ∧
      publicAPI.handoff.directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ]

/-- Canonical theorem-facing package extracted from the stable downstream public
API leaf. -/
def euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage S :=
  { publicAPI := euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPI S
    statusLinks :=
      euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPISmoke_statusLinks S
    endpointLinks :=
      euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPISmoke_endpointLinks S
    routeMarkers :=
      euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPISmoke_routeMarkers S
    endpointPackage :=
      euclideanYangMillsCompleteConstructionDirectBoundedDownstreamPublicAPISmoke_endpointPackage S }

/-- Projection from the theorem package to the canonical public status marker. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage_status
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage S).publicAPI.rootBundle.certificate.publicHandoffStatus =
      "direct-bare-M-primary-route-backed-compatibility" := by
  exact
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage S).routeMarkers.1

/-- Projection from the theorem package to the canonical endpoint-name list. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage_endpointNames
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage S).publicAPI.rootBundle.certificate.directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] := by
  exact
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage S).endpointPackage.1

/-- Projection from the theorem package to the canonical route markers. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage_routeMarkers
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
        "bare-M-direct-bundle" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
        "compatibility-only" := by
  exact ⟨
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage S).routeMarkers.2.2.2.1,
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage S).routeMarkers.2.2.2.2⟩

/-- Combined theorem-package projection for downstream callers. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage_complete
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage S).publicAPI.rootBundle.certificate.publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" ∧
      (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage S).publicAPI.rootBundle.certificate.directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
        "bare-M-direct-bundle" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
        "compatibility-only" := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage_status S,
    euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage_endpointNames S,
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage_routeMarkers S).1,
    (euclideanYangMillsCompleteConstructionDirectBoundedDownstreamTheoremPackage_routeMarkers S).2⟩

end

end MathlibAnalytic
end MGAP4D
