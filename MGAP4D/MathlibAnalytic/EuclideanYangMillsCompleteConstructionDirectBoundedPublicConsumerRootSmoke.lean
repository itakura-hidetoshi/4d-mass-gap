import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedPublicConsumerAPI
import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Root-level smoke surface for the public consumer API of the complete Yang--Mills
direct bounded route.

This file connects the compact public consumer theorem package to the existing
root public API bundle.  It consumes certified theorem surfaces and does not
re-destructure the large construction package.

It does not add a new spectral theorem invocation, spectral projection
construction, functional-calculus layer, numerical gap bound, or final
Yang--Mills mass-gap claim.
-/

/-- Root route-marker smoke proposition for the public consumer surface. -/
abbrev euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootRouteSmokeProp
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) : Prop :=
    (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle S).certificate.publicHandoffStatus =
        "direct-bare-M-primary-route-backed-compatibility" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
        "bare-M-direct-bundle" ∧
      _root_.MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotient.r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
        "compatibility-only"

/-- Root route-marker smoke theorem for the public consumer surface. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootRouteSmoke
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootRouteSmokeProp S := by
  exact euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle_route_markers S

/-- Root endpoint-name smoke proposition for the public consumer surface. -/
abbrev euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootEndpointSmokeProp
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) : Prop :=
    (euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle S).certificate.directEndpointNames =
      [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
        "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
        "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ]

/-- Root endpoint-name smoke theorem for the public consumer surface. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootEndpointSmoke
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootEndpointSmokeProp S := by
  exact euclideanYangMillsCompleteConstructionDirectBoundedRootPublicAPIBundle_endpoint_names S

/-- Complete root smoke proposition for compact public consumer users. -/
abbrev euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootSmokeProp
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) : Prop :=
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerFullAPIProp S ∧
      euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootRouteSmokeProp S ∧
      euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootEndpointSmokeProp S

/-- Complete root smoke theorem for compact public consumer users. -/
theorem euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootSmoke
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootSmokeProp S := by
  exact ⟨
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerFullAPI S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootRouteSmoke S,
    euclideanYangMillsCompleteConstructionDirectBounded_publicConsumerRootEndpointSmoke S⟩

end

end MathlibAnalytic
end MGAP4D
