# Mathlib Hilbert Rayleigh interface CI request

Branch: main

This note requests CI confirmation for the first post-adoption Hilbert/Rayleigh interface surface.

## Target artifacts

```text
MGAP4D/MathlibAnalytic/HilbertRayleighInterface.lean
MGAP4D/MathlibAnalytic.lean
docs/mathlib_hilbert_rayleigh_interface.md
```

## Expected checks

```text
Mathlib-backed main build
roots := #[`MGAP4D, `MGAP4D.MathlibAnalytic]
HilbertRayleighInterface builds
singletonHilbertRayleighInterface.ready builds
HilbertRayleighInterfaceReviewSurface.ready builds
final release remains held
```

## Boundary

```text
interface-level Hilbert/Rayleigh surface only
not yet full Hilbert-space Rayleigh quotient theorem
not yet full self-adjoint H_phys theorem
not yet full spectral theorem integration
not yet full projection-valued-measure theorem
public theorem boundary held
```
