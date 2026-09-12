import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorRouteBackedMigrationIndex
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace EuclideanYangMillsR4HilbertReconstructionQuotient

/-!
Public handoff index for the bounded actual R4 operator API.

This file records the public migration surface after the direct bare-`M` bundle
became the primary endpoint.  It deliberately imports only the local migration
index, not the aggregate `MGAP4D.MathlibAnalytic` root.
-/

/-- Machine-readable public handoff status for the bounded actual operator API. -/
def r4HilbertMathlibSelfAdjointOperator_direct_bounded_public_handoff_status : String :=
  "direct-bare-M-primary-route-backed-compatibility"

/-- Public handoff status is the direct bare-`M` primary route. -/
theorem r4HilbertMathlibSelfAdjointOperator_direct_bounded_public_handoff_status_eq :
    r4HilbertMathlibSelfAdjointOperator_direct_bounded_public_handoff_status =
      "direct-bare-M-primary-route-backed-compatibility" := by
  rfl

/-- The public handoff exposes the direct primary route and keeps route-backed names compatible. -/
theorem r4HilbertMathlibSelfAdjointOperator_direct_bounded_public_handoff_index :
    r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route =
        "bare-M-direct-bundle" ∧
      r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_role =
        "compatibility-only" ∧
      r4HilbertMathlibSelfAdjointOperator_preferred_bounded_actual_data_endpoint =
        "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data" ∧
      r4HilbertMathlibSelfAdjointOperator_preferred_full_domain_data_endpoint =
        "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data" ∧
      r4HilbertMathlibSelfAdjointOperator_preferred_domain_package_endpoint =
        "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" := by
  exact ⟨
    r4HilbertMathlibSelfAdjointOperator_boundedness_primary_route_is_direct,
    r4HilbertMathlibSelfAdjointOperator_route_backed_boundedness_is_compatibility_only,
    r4HilbertMathlibSelfAdjointOperator_preferred_bounded_actual_data_endpoint_is_direct,
    r4HilbertMathlibSelfAdjointOperator_preferred_full_domain_data_endpoint_is_direct,
    r4HilbertMathlibSelfAdjointOperator_preferred_domain_package_endpoint_is_direct⟩

/-- Machine-readable public endpoint list. -/
def r4HilbertMathlibSelfAdjointOperator_direct_bounded_public_endpoint_names : List String :=
  [ r4HilbertMathlibSelfAdjointOperator_preferred_bounded_actual_data_endpoint,
    r4HilbertMathlibSelfAdjointOperator_preferred_full_domain_data_endpoint,
    r4HilbertMathlibSelfAdjointOperator_preferred_domain_package_endpoint ]

/-- The public endpoint list is exactly the direct bare-`M` endpoint list. -/
theorem r4HilbertMathlibSelfAdjointOperator_direct_bounded_public_endpoint_names_eq :
    r4HilbertMathlibSelfAdjointOperator_direct_bounded_public_endpoint_names =
      [ "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data",
        "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data",
        "r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package" ] := by
  rfl

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
