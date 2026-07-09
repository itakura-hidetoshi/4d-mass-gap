# Direct boundedness public handoff

This PR adds a local Lean handoff index for the bounded actual R4 operator API.

The public migration surface records that:

- the primary boundedness route is `bare-M-direct-bundle`
- route-backed boundedness names are compatibility-only
- the preferred bounded actual data endpoint is `r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data`
- the preferred full-domain continuous endpoint is `r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data`
- the preferred bounded-domain package endpoint is `r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package`

The Lean file imports only the local migration index and avoids the aggregate `MGAP4D.MathlibAnalytic` root target.
