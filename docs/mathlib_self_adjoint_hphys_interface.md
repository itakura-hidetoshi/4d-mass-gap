# Mathlib self-adjoint H_phys interface surface

Branch: main

This note records the first operator-facing interface toward the full self-adjoint H_phys theorem.

## Lean artifacts

```text
MGAP4D/MathlibAnalytic/SelfAdjointHPhysInterface.lean
MGAP4D/MathlibAnalytic.lean
```

## Added surface

```text
MathlibAnalytic.SelfAdjointHPhysInterface
MathlibAnalytic.SelfAdjointHPhysInterface.ready
MathlibAnalytic.singletonSelfAdjointHPhysInterface
MathlibAnalytic.singleton_self_adjoint_hphys_interface_ready
MathlibAnalytic.singleton_self_adjoint_hphys_interface_symmetric
MathlibAnalytic.singleton_self_adjoint_hphys_interface_witness_attains
MathlibAnalytic.singleton_self_adjoint_hphys_interface_lower_bound
MathlibAnalytic.SelfAdjointHPhysReviewSurface
MathlibAnalytic.SelfAdjointHPhysReviewSurface.ready
MathlibAnalytic.selfAdjointHPhysReviewSurface
MathlibAnalytic.self_adjoint_hphys_review_surface_ready
MathlibAnalytic.self_adjoint_hphys_review_surface_final_release_held
```

## Meaning

```text
operator carrier is explicit
inner pairing is explicit
H_phys map is explicit
symmetry witness is explicit
Rayleigh interface compatibility is explicit
witness state attains 33/20
all admissible mapped states satisfy the Rayleigh lower bound
Hilbert/Rayleigh interface is linked to operator-shaped H_phys interface
main is Mathlib-backed
final release remains held
```

## Boundary

```text
operator-shaped interface only
not yet full unbounded self-adjoint operator theorem
not yet full spectral theorem integration
not yet full projection-valued-measure theorem
final theorem release not opened
public theorem boundary held
```
