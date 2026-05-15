# Mathlib physical unbounded-operator skeleton

Branch: main

This note records the physical unbounded-operator skeleton after the Hilbert-space instance skeleton.

## Lean artifacts

```text
MGAP4D/MathlibAnalytic/PhysicalUnboundedOperatorSkeleton.lean
MGAP4D/MathlibAnalytic.lean
```

## Added surface

```text
MathlibAnalytic.PhysicalUnboundedOperatorSkeletonData
MathlibAnalytic.PhysicalUnboundedOperatorSkeletonData.ready
MathlibAnalytic.physical_unbounded_operator_domain_preserved
MathlibAnalytic.physical_unbounded_operator_symmetric_on_domain
MathlibAnalytic.physical_unbounded_operator_self_adjoint_certificate
MathlibAnalytic.physical_unbounded_operator_rayleigh_lower_bound
MathlibAnalytic.physical_unbounded_operator_distinguished_attains_exact
MathlibAnalytic.prototypePhysicalUnboundedOperatorSkeletonData
MathlibAnalytic.prototype_physical_unbounded_operator_skeleton_ready
MathlibAnalytic.PhysicalUnboundedOperatorSkeletonReviewSurface
MathlibAnalytic.PhysicalUnboundedOperatorSkeletonReviewSurface.ready
MathlibAnalytic.physicalUnboundedOperatorSkeletonReviewSurface
MathlibAnalytic.physical_unbounded_operator_skeleton_review_surface_ready
```

## Meaning

```text
Hilbert-space instance skeleton is linked to physical unbounded-operator skeleton
physical domain is explicit
H_phys is explicit
domain is preserved by H_phys
H_phys is symmetric on the declared domain
self-adjoint certificate surface is present
Rayleigh lower bound is present
distinguished state attains exact value 33/20
```

## Boundary

```text
physical unbounded-operator skeleton only
not yet concrete Yang-Mills Hamiltonian construction
not yet spectral realization construction
not final theorem release
public theorem boundary held
```
