# Mathlib spectral-mass real surface

Branch: `mathlib-adoption/exact-gap-analytic`
PR: #10

This note records the Mathlib-backed real-order prototype for the observable-side positive spectral mass at the exact gap.

## Lean artifacts

```text
MGAP4D/MathlibAnalytic/SpectralMassReal.lean
MGAP4D.lean
```

## Added surface

```text
MathlibAnalytic.exactGapSpectralMassReal
MathlibAnalytic.exactGapSpectralMassReal_pos
MathlibAnalytic.exactGapSpectralMassReal_ne_zero
MathlibAnalytic.PositiveSpectralMassAtExactGap
MathlibAnalytic.positive_spectral_mass_at_exact_gap_prototype
MathlibAnalytic.positive_spectral_mass_location_eq_3320
MathlibAnalytic.positive_spectral_mass_nonzero
MathlibAnalytic.exists_positive_spectral_mass_at_exact_gap
MathlibAnalytic.SpectralMassRealSurface
MathlibAnalytic.spectralMassRealSurface
MathlibAnalytic.SpectralMassRealSurface.ready
MathlibAnalytic.spectral_mass_real_surface_ready
MathlibAnalytic.spectral_mass_real_surface_value
MathlibAnalytic.spectral_mass_real_surface_positive_mass
MathlibAnalytic.spectral_mass_real_surface_nonzero_mass
MathlibAnalytic.spectral_mass_real_surface_exists_positive_mass
MathlibAnalytic.spectral_mass_real_surface_attainment_compatible
```

## Meaning

```text
exactGapSpectralMassReal = 1
0 < exactGapSpectralMassReal
exactGapSpectralMassReal != 0
PositiveSpectralMassAtExactGap value mass := value = 33/20 and 0 < mass
there exists a positive real spectral mass at 33/20
positive mass is compatible with Rayleigh exact-gap attainment
```

## Boundary

```text
Mathlib-backed real spectral-mass prototype only
not yet full projection-valued-measure theorem
main remains pre-Mathlib
final theorem release not opened
public theorem boundary held
```
