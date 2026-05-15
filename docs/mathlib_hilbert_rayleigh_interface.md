# Mathlib Hilbert Rayleigh interface surface

Branch: main

This note records the first post-adoption interface toward the full Hilbert-space Rayleigh theorem.

## Lean artifacts

```text
MGAP4D/MathlibAnalytic/HilbertRayleighInterface.lean
MGAP4D/MathlibAnalytic.lean
```

## Added surface

```text
MathlibAnalytic.HilbertRayleighInterface
MathlibAnalytic.HilbertRayleighInterface.attainsExactGap
MathlibAnalytic.HilbertRayleighInterface.ready
MathlibAnalytic.singletonHilbertRayleighInterface
MathlibAnalytic.singleton_hilbert_rayleigh_interface_ready
MathlibAnalytic.singleton_hilbert_rayleigh_interface_attains
MathlibAnalytic.singleton_hilbert_rayleigh_interface_lower_bound
MathlibAnalytic.HilbertRayleighInterfaceReviewSurface
MathlibAnalytic.HilbertRayleighInterfaceReviewSurface.ready
MathlibAnalytic.hilbertRayleighInterfaceReviewSurface
MathlibAnalytic.hilbert_rayleigh_interface_review_surface_ready
MathlibAnalytic.hilbert_rayleigh_interface_review_surface_final_release_held
```

## Meaning

```text
state carrier is explicit
Rayleigh-energy map into Real is explicit
admissibility predicate is explicit
witness state is explicit
witness attains 33/20
all admissible states satisfy the lower bound
real analytic closure is linked to the abstract Hilbert/Rayleigh interface
main is Mathlib-backed
final release remains held
```

## Boundary

```text
interface-level Hilbert/Rayleigh surface only
not yet full Hilbert-space Rayleigh quotient theorem
not yet full self-adjoint H_phys theorem
not yet full spectral theorem integration
not yet full projection-valued-measure theorem
final theorem release not opened
public theorem boundary held
```
