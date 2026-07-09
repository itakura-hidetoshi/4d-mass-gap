import MGAP4D.MathlibAnalytic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Root smoke for the complete Yang--Mills direct bounded certificate.

This file checks that the aggregate `MGAP4D.MathlibAnalytic` import exposes the
certificate surface added after the direct bare-`M` boundedness handoff.  It does
not add a new spectral theorem, spectral projection construction, numerical gap
bound, or final mass-gap claim.
-/

/-- The aggregate root exposes the complete construction direct bounded
certificate constructor. -/
def euclideanYangMillsCompleteConstructionDirectBoundedRootCertificateSmoke
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsCompleteConstructionDirectBoundedCertificate S :=
  euclideanYangMillsCompleteConstructionDirectBoundedCertificate S

/-- The aggregate root exposes the complete construction full spectral package
projection supplied by the certificate surface. -/
def euclideanYangMillsCompleteConstructionDirectBoundedRootFullSpectralSmoke
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :=
  euclidean_yang_mills_complete_construction_direct_bounded_full_spectral_package S
    (euclideanYangMillsCompleteConstructionDirectBoundedCertificate S)

/-- The aggregate root exposes the public handoff status theorem. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedRootStatusSmoke
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedCertificate S).publicHandoffStatus =
      "direct-bare-M-primary-route-backed-compatibility" := by
  exact
    (euclidean_yang_mills_complete_construction_direct_bounded_public_handoff S
      (euclideanYangMillsCompleteConstructionDirectBoundedCertificate S)).1

/-- The aggregate root exposes the fact that the direct bare-`M` bundle is the
primary boundedness route. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedRootPrimaryRouteSmoke
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
      "bare-M-direct-bundle" := by
  exact
    (euclidean_yang_mills_complete_construction_direct_bounded_public_handoff S
      (euclideanYangMillsCompleteConstructionDirectBoundedCertificate S)).2.1

/-- The aggregate root exposes the compatibility-only status of route-backed
boundedness names. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedRootCompatibilitySmoke
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
      "compatibility-only" := by
  exact
    (euclidean_yang_mills_complete_construction_direct_bounded_public_handoff S
      (euclideanYangMillsCompleteConstructionDirectBoundedCertificate S)).2.2.1

/-- The aggregate root exposes the preferred direct bounded public endpoint
list. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedRootEndpointNamesSmoke
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedCertificate S).directEndpointNames =
      [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
        "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
        "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] := by
  exact
    (euclidean_yang_mills_complete_construction_direct_bounded_public_handoff S
      (euclideanYangMillsCompleteConstructionDirectBoundedCertificate S)).2.2.2

end

end MathlibAnalytic
end MGAP4D
