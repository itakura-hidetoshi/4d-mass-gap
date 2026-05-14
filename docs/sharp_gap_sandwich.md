# Sharp gap sandwich

This note records a pre-Mathlib sharp-gap sandwich certificate.

## Lean artifacts

```text
MGAP4D/Spectral/SharpGapSandwich.lean
MGAP4D/Spectral.lean
MGAP4D/SharpGapFinalSpineBridge.lean
MGAP4D.lean
```

## Added surface

```text
SharpGapSandwichCertificate
SharpGapSandwichCertificate.ready
sharpGapSandwich3320Certificate
sharp_gap_sandwich_certificate_pack
sharp_gap_sandwich_3320_ready
sharp_gap_sandwich_3320_exact_value
sharp_gap_sandwich_3320_lower_bound_value
sharp_gap_sandwich_3320_eigenvalue
sharp_gap_sandwich_3320_eigen_witness_orthogonal
sharp_gap_sandwich_3320_eigen_witness_not_vacuum
sharp_gap_sandwich_3320_release_held
sharp_gap_sandwich_3320_public_boundary_locked
SharpGapFinalSpineBridge
SharpGapFinalSpineBridge.ready
sharpGapFinalSpineBridge3320
sharp_gap_final_spine_bridge_3320_ready
final_spine_sharp_gap_sandwich_ready
final_spine_sharp_gap_exact_value_3320
final_spine_sharp_gap_lower_bound_value_3320
final_spine_sharp_gap_eigen_witness_value_3320
final_spine_sharp_gap_eigen_witness_orthogonal
final_spine_sharp_gap_eigen_witness_not_vacuum
final_spine_sharp_gap_release_held
final_spine_sharp_gap_public_boundary_locked
```

## Meaning

The certificate packages lower-bound and eigen-witness routes into an exact-gap tracking surface.

```text
lower-bound route ready
lower-bound value = 33/20
physical eigen-witness ready
physical eigen-witness value = 33/20
physical eigen-witness is orthogonal
physical eigen-witness is not vacuum
R1--R7 theorem-obligation completion ready
R4 lower-bound route complete
R5 spectrum-infimum route complete
R6 interval-exclusion route complete
R7 atom-exact route complete
gap upper bound from eigen-witness visible
gap lower bound from R1--R7 visible
exact gap value = 33/20
sharp gap sandwich visible
final release held
public boundary locked
```

## Boundary

```text
pre-Mathlib structural sharp-gap sandwich only
exact-gap tracking surface visible
final theorem release not opened
Mathlib on main not introduced
public theorem boundary held
```
