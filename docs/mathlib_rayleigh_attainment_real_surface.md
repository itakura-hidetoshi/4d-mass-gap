# Mathlib Rayleigh attainment real surface

Branch: `mathlib-adoption/exact-gap-analytic`
PR: #10

This note records the Mathlib-backed real-order attainment companion to the Rayleigh lower-bound prototype.

## Lean artifacts

```text
MGAP4D/MathlibAnalytic/RayleighAttainmentReal.lean
MGAP4D.lean
```

## Added surface

```text
MathlibAnalytic.RayleighAttainsExactGap
MathlibAnalytic.exact_gap_value_attains_rayleigh
MathlibAnalytic.exists_rayleigh_exact_gap_attainment
MathlibAnalytic.rayleigh_attainment_energy_eq_3320
MathlibAnalytic.RayleighAttainmentRealSurface
MathlibAnalytic.rayleighAttainmentRealSurface
MathlibAnalytic.RayleighAttainmentRealSurface.ready
MathlibAnalytic.rayleigh_attainment_real_surface_ready
MathlibAnalytic.rayleigh_attainment_real_surface_value
MathlibAnalytic.rayleigh_attainment_real_surface_witness_admissible
MathlibAnalytic.rayleigh_attainment_real_surface_witness_attains_value
MathlibAnalytic.rayleigh_attainment_real_surface_lower_bound
MathlibAnalytic.rayleigh_attainment_real_surface_exists_attainment
MathlibAnalytic.rayleigh_attainment_real_surface_positive
```

## Meaning

```text
RayleighAttainsExactGap energy := RayleighEnergyAdmissible energy and energy = 33/20
33/20 attains the Rayleigh lower-bound prototype
there exists an admissible Rayleigh energy attaining the exact gap
any attaining energy has value 33/20
```

## Boundary

```text
Mathlib-backed real Rayleigh attainment prototype only
not yet full Hilbert-space eigenvector/Rayleigh theorem
main remains pre-Mathlib
final theorem release not opened
public theorem boundary held
```
