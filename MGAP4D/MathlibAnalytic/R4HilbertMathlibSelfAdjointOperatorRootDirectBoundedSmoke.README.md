# Direct boundedness smoke

This PR adds a Lean compile smoke confirming that the local direct bare-`M` boundedness API is importable without forcing the aggregate `MGAP4D.MathlibAnalytic` root target.

The checked surface is:

- direct bare-`M` bundle
- direct bare-`M` bounded actual data
- direct bare-`M` bounded-domain package
- migration marker: primary route is `bare-M-direct-bundle`
- migration marker: route-backed boundedness is `compatibility-only`

This file is intentionally documentation-only and not imported by Lean.