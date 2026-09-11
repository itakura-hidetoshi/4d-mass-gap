import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle
import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Bridge from the root public API bundle to the ordered public surface.

The root public API bundle was merged after the ordered public surface.  This
file connects the two theorem-facing surfaces without rewriting history: the
bundle certificate and the ordered-surface root public certificate are the same
canonical certificate, and their direct bounded route markers agree.

It does not add a spectral theorem invocation, spectral projection construction,
functional-calculus layer, numerical gap bound, or final Yang--Mills mass-gap
claim.
-/

/-- The root public API bundle certificate agrees definitionally with the ordered
public surface root certificate. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedBundleOrderedBridge_certificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle S).certificate =
      (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface S).rootPublicCertificate := by
  rfl

/-- The root public API bundle status marker agrees with the ordered public
surface root status marker. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedBundleOrderedBridge_status
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle S).certificate.publicHandoffStatus =
      (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface S).rootPublicCertificate.publicHandoffStatus := by
  rw [euclideanYangMillsCompleteConstructionDirectBoundedBundleOrderedBridge_certificate S]

/-- The root public API bundle endpoint-name list agrees with the ordered public
surface root endpoint-name list. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedBundleOrderedBridge_endpointNames
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle S).certificate.directEndpointNames =
      (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface S).rootPublicCertificate.directEndpointNames := by
  rw [euclideanYangMillsCompleteConstructionDirectBoundedBundleOrderedBridge_certificate S]

/-- The root public API bundle and ordered public surface share the canonical
status marker. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedBundleOrderedBridge_statusPackage
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle S).certificate.publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" ∧
      (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface S).rootPublicCertificate.publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle_status S,
    (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface_status S
      (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface S)).1⟩

/-- The root public API bundle and ordered public surface share the canonical
endpoint-name list. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedBundleOrderedBridge_endpointPackage
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle S).certificate.directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] ∧
      (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface S).rootPublicCertificate.directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle_endpoint_names S,
    (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface_endpointNames S
      (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface S)).1⟩

/-- Combined downstream route-marker bridge after the late bundle merge. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedBundleOrderedBridge_routeMarkers
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle S).certificate.publicHandoffStatus =
        (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface S).rootPublicCertificate.publicHandoffStatus ∧
      (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle S).certificate.directEndpointNames =
        (euclideanYangMillsCompleteConstructionDirectBoundedOrderedPublicSurface S).rootPublicCertificate.directEndpointNames ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
        "bare-M-direct-bundle" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
        "compatibility-only" := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedBundleOrderedBridge_status S,
    euclideanYangMillsCompleteConstructionDirectBoundedBundleOrderedBridge_endpointNames S,
    euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle_primary_route S,
    euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle_compatibility_role S⟩

end

end MathlibAnalytic
end MGAP4D
