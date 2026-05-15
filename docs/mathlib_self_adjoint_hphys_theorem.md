# Mathlib self-adjoint H_phys theorem body

Branch: main

This note records the second post-interface theorem-body step: the abstract self-adjoint H_phys theorem body.

## Lean artifacts

```text
MGAP4D/MathlibAnalytic/SelfAdjointHPhysTheorem.lean
MGAP4D/MathlibAnalytic.lean
```

## Added theorem body

```text
MathlibAnalytic.SelfAdjointHPhysTheoremData
MathlibAnalytic.SelfAdjointHPhysTheoremData.ready
MathlibAnalytic.self_adjoint_hphys_symmetric_on_domain
MathlibAnalytic.self_adjoint_hphys_domain_closed
MathlibAnalytic.self_adjoint_hphys_certificate
MathlibAnalytic.self_adjoint_hphys_rayleigh_lower_bound
MathlibAnalytic.self_adjoint_hphys_witness_rayleigh_attains
MathlibAnalytic.singletonSelfAdjointHPhysTheoremData
MathlibAnalytic.singleton_self_adjoint_hphys_theorem_data_ready
MathlibAnalytic.singleton_self_adjoint_hphys_symmetric_on_domain
MathlibAnalytic.singleton_self_adjoint_hphys_rayleigh_lower_bound
MathlibAnalytic.SelfAdjointHPhysTheoremReviewSurface
MathlibAnalytic.SelfAdjointHPhysTheoremReviewSurface.ready
MathlibAnalytic.selfAdjointHPhysTheoremReviewSurface
MathlibAnalytic.self_adjoint_hphys_theorem_review_surface_ready
MathlibAnalytic.self_adjoint_hphys_theorem_review_surface_final_release_held
```

## Meaning

```text
operator domain is explicit
H_phys is explicit
symmetry on domain is explicit
domain closure under H_phys is explicit
self-adjointness certificate surface is explicit
Rayleigh quotient compatibility is explicit
witness attains 33/20 through the Rayleigh quotient body
self-adjoint H_phys theorem body is closed at abstract theorem-body level
```

## Boundary

```text
abstract self-adjoint H_phys theorem body only
not yet concrete unbounded operator realization
not yet full spectral theorem integration theorem body
not final theorem release
public theorem boundary held
```
