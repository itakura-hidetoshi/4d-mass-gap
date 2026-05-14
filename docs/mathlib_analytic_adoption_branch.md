# Mathlib analytic adoption branch

Branch: `mathlib-adoption/exact-gap-analytic`

This branch starts the controlled resolution of the pre-Mathlib boundary.

## Purpose

```text
Introduce Mathlib on a separate adoption branch.
Keep main pre-Mathlib.
Open the analytic replacement surface for exact-gap theorem bodies.
Do not open final theorem release.
Preserve public theorem boundary.
```

## Changes

```text
lakefile.lean: add require mathlib from git
MGAP4D/MathlibAnalytic/Basic.lean: minimal import Mathlib surface
MGAP4D.lean: import MGAP4D.MathlibAnalytic.Basic on adoption branch only
.github/workflows/lean-direct-elan.yml: enable branch CI
```

## Added Lean surface

```text
MathlibAnalytic.MathlibImportSurface
MathlibAnalytic.mathlibImportSurface
MathlibAnalytic.MathlibImportSurface.ready
MathlibAnalytic.mathlib_import_surface_ready
MathlibAnalytic.exactGapValueReal
MathlibAnalytic.exactGapValueReal_pos
MathlibAnalytic.exactGapValueReal_eq
```

## CI trigger note

```text
This update intentionally touches the adoption branch after enabling branch CI.
It should trigger the Lean Direct Elan CI on mathlib-adoption/exact-gap-analytic.
```

## Boundary

```text
Mathlib introduced only on branch mathlib-adoption/exact-gap-analytic
main remains pre-Mathlib
analytic replacement is not yet final release
public boundary remains held
```
