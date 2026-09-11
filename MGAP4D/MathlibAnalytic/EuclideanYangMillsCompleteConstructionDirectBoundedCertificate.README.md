# Complete Yang–Mills direct bounded certificate

This PR adds a local Lean certificate layer that bundles the existing finite-volume/continuum Yang–Mills construction certificate with the direct bounded R4 operator public handoff.

The certificate keeps two surfaces together:

- the construction-spine full spectral package already exposed by `EuclideanYangMillsContinuumMeasureConstructionCertificate`
- the direct bare-`M` boundedness public handoff introduced by the bounded actual R4 operator API

The route-backed boundedness names remain compatibility-only.  This PR does not add a new spectral theorem, spectral projection construction, or numerical mass-gap claim.
