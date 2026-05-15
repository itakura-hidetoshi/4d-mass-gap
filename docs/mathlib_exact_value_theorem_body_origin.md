# Mathlib exact value theorem-body origin

Branch: main

This note records that the value `33/20` is treated as coming from the theorem-body closure itself, not from a packaging artifact, documentation artifact, CI ledger, manifest, or prototype-only release wrapper.

## Lean artifacts

```text
MGAP4D/MathlibAnalytic/ExactValueTheoremBodyOrigin.lean
MGAP4D.lean
```

## Theorem-body chain used

```text
Hilbert Rayleigh quotient body
self-adjoint H_phys body
spectral theorem body
PVM body
observable atom body
compact plaquette construction body
operator-measure compatibility body
```

## Source theorem-body closure

```text
ExactGapTheoremBodyClosure.ready
exact_gap_theorem_body_closure_value
exact_gap_theorem_body_closure_positive
exact_gap_theorem_body_closure_weight_positive
exact_gap_theorem_body_closure_weight_nonzero
exact_gap_theorem_body_closure_weight_equals_pvm_mass
```

## Added surface

```text
MathlibAnalytic.ExactValueTheoremBodyOriginData
MathlibAnalytic.ExactValueTheoremBodyOriginData.ready
MathlibAnalytic.exact_value_origin_from_theorem_body
MathlibAnalytic.exact_value_origin_positive_from_theorem_body
MathlibAnalytic.exact_value_origin_weight_positive_from_theorem_body
MathlibAnalytic.exact_value_origin_not_packaging_artifact
MathlibAnalytic.exact_value_origin_not_ci_ledger_artifact
MathlibAnalytic.prototypeExactValueTheoremBodyOriginData
MathlibAnalytic.prototype_exact_value_theorem_body_origin_ready
MathlibAnalytic.ExactValueTheoremBodyOriginReviewSurface
MathlibAnalytic.ExactValueTheoremBodyOriginReviewSurface.ready
MathlibAnalytic.exactValueTheoremBodyOriginReviewSurface
MathlibAnalytic.exact_value_theorem_body_origin_review_surface_ready
```

## Meaning

```text
33/20 is read from ExactGapTheoremBodyClosure.exactValue_eq_3320
33/20 is not treated as a packaging artifact
33/20 is not treated as a documentation artifact
33/20 is not treated as a CI-ledger artifact
33/20 is not treated as manifest-only
observable spectral weight positivity and PVM mass compatibility are carried from theorem body
physical Hamiltonian normalization bridge remains unchanged
public theorem boundary is held
```

## Boundary

```text
theorem-body origin certificate only
theorem body unchanged
normalization bridge unchanged
external consensus is not claimed
public theorem boundary held
```
