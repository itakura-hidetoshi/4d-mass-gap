import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorRouteBackedBoundednessCompatibility
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace EuclideanYangMillsR4HilbertReconstructionQuotient

/-!
Migration index for the bounded actual R4 operator API.

The primary endpoint is now the direct bare-`M` bundle surface.  Route-backed
boundedness names remain available only as compatibility surfaces for older
call sites.
-/

/-- Machine-readable marker for the primary boundedness route. -/
def r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route : String :=
  "bare-M-direct-bundle"

/-- Machine-readable marker for the legacy route-backed boundedness role. -/
def r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role : String :=
  "compatibility-only"

/-- The boundedness primary route is the direct bare-`M` bundle. -/
theorem r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route_is_direct :
    r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
      "bare-M-direct-bundle" := by
  rfl

/-- Route-backed boundedness names are retained only as compatibility surfaces. -/
theorem r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_is_compatibility_only :
    r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
      "compatibility-only" := by
  rfl

/-- Preferred direct endpoint name for bounded actual data. -/
def r4HilbertMathlibSelfAdjointOperator_preferred_bounded_actual_data_endpoint : String :=
  "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data"

/-- Preferred direct endpoint name for full-domain continuous data. -/
def r4HilbertMathlibSelfAdjointOperator_preferred_full_domain_data_endpoint : String :=
  "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data"

/-- Preferred direct endpoint name for the bounded-domain package. -/
def r4HilbertMathlibSelfAdjointOperator_preferred_domain_package_endpoint : String :=
  "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package"

/-- The preferred bounded actual data endpoint is the direct bare-`M` bundle endpoint. -/
theorem r4HilbertMathlibSelfAdjointOperator_preferred_bounded_actual_data_endpoint_is_direct :
    r4HilbertMathlibSelfAdjointOperator_preferred_bounded_actual_data_endpoint =
      "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data" := by
  rfl

/-- The preferred full-domain data endpoint is the direct bare-`M` bundle endpoint. -/
theorem r4HilbertMathlibSelfAdjointOperator_preferred_full_domain_data_endpoint_is_direct :
    r4HilbertMathlibSelfAdjointOperator_preferred_full_domain_data_endpoint =
      "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data" := by
  rfl

/-- The preferred domain package endpoint is the direct bare-`M` bundle endpoint. -/
theorem r4HilbertMathlibSelfAdjointOperator_preferred_domain_package_endpoint_is_direct :
    r4HilbertMathlibSelfAdjointOperator_preferred_domain_package_endpoint =
      "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" := by
  rfl

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
