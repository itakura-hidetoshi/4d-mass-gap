import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedRootSmoke
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Stable public API for the complete Yang--Mills direct bounded certificate root
exposure.

This layer sits above the root-smoke leaf and provides theorem-facing names for
downstream files.  It deliberately imports the smoke leaf, not the aggregate
`MGAP4D.MathlibAnalytic` root, so changed-file CI does not replay unrelated
legacy aggregate-root failures.

It does not add a spectral theorem invocation, spectral projection construction,
functional-calculus layer, numerical gap bound, or final Yang--Mills mass-gap
claim.
-/

/-- Public API constructor for the complete construction direct bounded
certificate. -/
def euclideanYangMillsCompleteConstructionDirectBoundedRootPublicCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsCompleteConstructionDirectBoundedCertificate S :=
  euclideanYangMillsCompleteConstructionDirectBoundedRootCertificateSmoke S

/-- Public API projection for the certificate-supplied full spectral package. -/
def euclideanYangMillsCompleteConstructionDirectBoundedRootPublicFullSpectralPackage
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :=
  euclideanYangMillsCompleteConstructionDirectBoundedRootFullSpectralSmoke S

/-- Public API theorem for the direct bounded handoff status marker. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedRootPublicStatus
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicCertificate S).publicHandoffStatus =
      "direct-bare-M-primary-route-backed-compatibility" := by
  exact euclideanYangMillsCompleteConstructionDirectBoundedRootStatusSmoke S

/-- Public API theorem recording the primary boundedness route. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedRootPublicPrimaryRoute
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
      "bare-M-direct-bundle" := by
  exact euclideanYangMillsCompleteConstructionDirectBoundedRootPrimaryRouteSmoke S

/-- Public API theorem recording that route-backed boundedness names are retained
as compatibility-only surfaces. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedRootPublicCompatibilityRole
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
      "compatibility-only" := by
  exact euclideanYangMillsCompleteConstructionDirectBoundedRootCompatibilitySmoke S

/-- Public API theorem for the preferred direct bare-`M` endpoint names. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedRootPublicEndpointNames
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicCertificate S).directEndpointNames =
      [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
        "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
        "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] := by
  exact euclideanYangMillsCompleteConstructionDirectBoundedRootEndpointNamesSmoke S

/-- Combined public route marker package for downstream theorem-surface imports. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedRootPublicRouteMarkers
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicCertificate S).publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
        "bare-M-direct-bundle" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
        "compatibility-only" := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedRootPublicStatus S,
    euclideanYangMillsCompleteConstructionDirectBoundedRootPublicPrimaryRoute S,
    euclideanYangMillsCompleteConstructionDirectBoundedRootPublicCompatibilityRole S⟩

end

end MathlibAnalytic
end MGAP4D
