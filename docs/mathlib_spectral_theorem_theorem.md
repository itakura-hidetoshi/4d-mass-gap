# Mathlib spectral theorem theorem body

Branch: main

This note records the third post-interface theorem-body step: abstract spectral theorem integration.

## Lean artifacts

```text
MGAP4D/MathlibAnalytic/SpectralTheoremTheorem.lean
MGAP4D/MathlibAnalytic.lean
```

## Added theorem body

```text
MathlibAnalytic.SpectralTheoremTheoremData
MathlibAnalytic.SpectralTheoremTheoremData.ready
MathlibAnalytic.spectral_theorem_exact_value_in_support
MathlibAnalytic.spectral_theorem_support_lower_bound
MathlibAnalytic.spectral_theorem_positive_mass_at_exact
MathlibAnalytic.spectral_theorem_nonzero_mass_at_exact
MathlibAnalytic.spectral_theorem_certificate
MathlibAnalytic.singletonSpectralTheoremTheoremData
MathlibAnalytic.singleton_spectral_theorem_theorem_data_ready
MathlibAnalytic.singleton_spectral_theorem_exact_value_in_support
MathlibAnalytic.singleton_spectral_theorem_support_lower_bound
MathlibAnalytic.singleton_spectral_theorem_positive_mass_at_exact
MathlibAnalytic.singleton_spectral_theorem_nonzero_mass_at_exact
MathlibAnalytic.SpectralTheoremTheoremReviewSurface
MathlibAnalytic.SpectralTheoremTheoremReviewSurface.ready
MathlibAnalytic.spectralTheoremTheoremReviewSurface
MathlibAnalytic.spectral_theorem_theorem_review_surface_ready
MathlibAnalytic.spectral_theorem_theorem_review_surface_final_release_held
```

## Meaning

```text
self-adjoint H_phys theorem body is linked to spectral support
spectral support is explicit
spectral mass is explicit
33/20 belongs to spectral support
all spectral support values are bounded below by 33/20
spectral mass at 33/20 is positive
spectral mass at 33/20 is nonzero
spectral theorem certificate surface is explicit
spectral theorem integration theorem body is closed at abstract theorem-body level
```

## Boundary

```text
abstract spectral theorem integration body only
not yet concrete spectral measure realization
not yet full projection-valued-measure theorem body
not final theorem release
public theorem boundary held
```
