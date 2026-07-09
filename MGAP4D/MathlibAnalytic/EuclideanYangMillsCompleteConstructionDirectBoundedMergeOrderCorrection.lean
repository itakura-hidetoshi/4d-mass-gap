import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedPublicHandoff
import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPI
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Merge-order correction layer for the complete Yang--Mills direct bounded public
surface.

PR #723 was merged before PR #722, although the intended conceptual order was
that the complete-construction public handoff layer from #722 should precede the
root public API leaf from #723.

This file does not rewrite history and does not add any new spectral theorem,
spectral projection construction, numerical gap bound, or final Yang--Mills
mass-gap claim.  It records, in Lean, that the final branch state has the desired
semantic order: the root public API and the complete-construction public handoff
project to the same direct bounded markers.
-/

/-- The root public API status agrees with the complete-construction public
handoff status after the reversed merge order. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedMergeOrderStatus_agrees
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicCertificate S).publicHandoffStatus =
      (euclideanYangMillsCompleteConstructionDirectBoundedPublicHandoff S).publicHandoffStatus := by
  calc
    (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicCertificate S).publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" :=
      euclideanYangMillsCompleteConstructionDirectBoundedRootPublicStatus S
    _ = (euclideanYangMillsCompleteConstructionDirectBoundedPublicHandoff S).publicHandoffStatus := by
      exact (euclidean_yang_mills_complete_construction_direct_bounded_public_handoff_status S).symm

/-- The root public API endpoint-name list agrees with the complete-construction
public handoff endpoint-name list after the reversed merge order. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedMergeOrderEndpointNames_agrees
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicCertificate S).directEndpointNames =
      (euclideanYangMillsCompleteConstructionDirectBoundedPublicHandoff S).directEndpointNames := by
  calc
    (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicCertificate S).directEndpointNames =
        [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
          "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] :=
      euclideanYangMillsCompleteConstructionDirectBoundedRootPublicEndpointNames S
    _ = (euclideanYangMillsCompleteConstructionDirectBoundedPublicHandoff S).directEndpointNames := by
      exact (euclidean_yang_mills_complete_construction_direct_bounded_endpoint_names S).symm

/-- The reversed merge order still leaves the public route markers in the intended
canonical direct bounded state. -/
theorem euclideanYangMillsCompleteConstructionDirectBoundedMergeOrderRouteMarkers
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicCertificate S).publicHandoffStatus =
        (euclideanYangMillsCompleteConstructionDirectBoundedPublicHandoff S).publicHandoffStatus ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
        "bare-M-direct-bundle" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
        "compatibility-only" ∧
      (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicCertificate S).directEndpointNames =
        (euclideanYangMillsCompleteConstructionDirectBoundedPublicHandoff S).directEndpointNames := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBoundedMergeOrderStatus_agrees S,
    euclideanYangMillsCompleteConstructionDirectBoundedRootPublicPrimaryRoute S,
    euclideanYangMillsCompleteConstructionDirectBoundedRootPublicCompatibilityRole S,
    euclideanYangMillsCompleteConstructionDirectBoundedMergeOrderEndpointNames_agrees S⟩

end

end MathlibAnalytic
end MGAP4D
