import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPI
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Bundle layer for the complete Yang--Mills direct bounded root public API.

This file packages the public API markers introduced below the aggregate root
into a single theorem-facing object for downstream files.  It imports only the
public API leaf, not the aggregate `MGAP4D.MathlibAnalytic` root, so changed-file
CI remains local to this direct bounded route surface.

It does not add a spectral theorem invocation, spectral projection construction,
functional-calculus layer, numerical gap bound, or final Yang--Mills mass-gap
claim.
-/

/-- Bundled public API receipts for the complete construction direct bounded
certificate root exposure. -/
structure EuclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) where
  certificate : EuclideanYangMillsCompleteConstructionDirectBoundedCertificate S
  status_eq :
    certificate.publicHandoffStatus =
      "direct-bare-M-primary-route-backed-compatibility"
  primaryRoute_eq :
    _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
      "bare-M-direct-bundle"
  compatibilityRole_eq :
    _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
      "compatibility-only"
  endpointNames_eq :
    certificate.directEndpointNames =
      [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
        "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
        "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ]

/-- Canonical bundled public API receipts for the complete construction direct
bounded certificate root exposure. -/
def euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle S where
  certificate := euclideanYangMillsCompleteConstructionDirectBoundedRootPublicCertificate S
  status_eq := euclideanYangMillsCompleteConstructionDirectBoundedRootPublicStatus S
  primaryRoute_eq := euclideanYangMillsCompleteConstructionDirectBoundedRootPublicPrimaryRoute S
  compatibilityRole_eq :=
    euclideanYangMillsCompleteConstructionDirectBoundedRootPublicCompatibilityRole S
  endpointNames_eq := euclideanYangMillsCompleteConstructionDirectBoundedRootPublicEndpointNames S

/-- Bundle projection for the direct bounded handoff status marker. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle_status
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle S).certificate.publicHandoffStatus =
      "direct-bare-M-primary-route-backed-compatibility" := by
  exact (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle S).status_eq

/-- Bundle projection for the primary direct bare-`M` boundedness route marker. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle_primary_route
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
      "bare-M-direct-bundle" := by
  exact (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle S).primaryRoute_eq

/-- Bundle projection for the compatibility-only route-backed boundedness marker. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle_compatibility_role
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
      "compatibility-only" := by
  exact (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle S).compatibilityRole_eq

/-- Bundle projection for the preferred direct bare-`M` endpoint names. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle_endpoint_names
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle S).certificate.directEndpointNames =
      [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
        "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
        "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] := by
  exact (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle S).endpointNames_eq

/-- Combined bundle projection for downstream route-marker imports. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle_route_markers
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle S).certificate.publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
        "bare-M-direct-bundle" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
        "compatibility-only" := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle_status S,
    euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle_primary_route S,
    euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle_compatibility_role S⟩

end

end MathlibAnalytic
end MGAP4D
