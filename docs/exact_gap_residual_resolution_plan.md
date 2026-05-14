# Exact gap residual resolution plan

This note records a pre-Mathlib resolution plan for the exact-gap residual map.

## Lean artifacts

```text
MGAP4D/ExactGapResidualResolutionPlan.lean
MGAP4D.lean
```

## Added surface

```text
ExactGapResidualResolutionTarget
ExactGapResidualResolutionPlan
ExactGapResidualResolutionPlan.ready
exactGap3320ResidualResolutionPlan
exact_gap_residual_resolution_plan_pack
exact_gap_3320_residual_resolution_plan_ready
exact_gap_3320_residual_resolution_plan_value
exact_gap_3320_residual_resolution_plan_release_held
exact_gap_3320_residual_resolution_plan_public_boundary_locked
exact_gap_3320_residual_resolution_plan_no_auto_release
exact_gap_3320_residual_resolution_plan_structural_first
exact_gap_3320_residual_resolution_plan_mathlib_last
```

## Meaning

The plan orders the seven residual replacement targets conservatively.

```text
residual map ready
structural surface realization planned
H_phys self-adjoint / semibounded / domain planned
gap-infimum definition planned
lower-bound proof body planned
eigenvector construction planned
observable spectral-projection theorem planned
Mathlib adoption bridge planned
conservative ordering visible
resolution plan visible
exact gap value = 33/20
final release held
public boundary locked
no automatic final release
```

## Resolution order

```text
1. structuralSurfaceRealization
2. hphysSelfAdjointSemiboundedDomain
3. gapInfimumDefinition
4. lowerBoundProofBody
5. eigenvectorConstruction
6. observableSpectralProjection
7. mathlibAdoptionBridge
```

## Boundary

```text
pre-Mathlib structural residual-resolution plan only
residuals are ordered and visible
final theorem release not opened
Mathlib on main not introduced
public theorem boundary held
```
