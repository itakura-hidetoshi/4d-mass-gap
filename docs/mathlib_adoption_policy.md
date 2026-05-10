# Mathlib Adoption Policy

MGAP4D currently builds as a minimal Lean 4 project. This keeps the GitHub migration lightweight while the active source tree is being assembled.

Mathlib should be added only when the first theorem-level concrete module truly requires library support.

## When to add Mathlib

Add Mathlib when migrating theorem-level modules involving:

- inner product spaces;
- closed subspaces;
- orthogonal projections;
- self-adjoint operators;
- spectrum and spectral order;
- Hilbert-space direct sums;
- closed forms and square-root routes.

## When not to add Mathlib

Do not add Mathlib for:

- status interfaces;
- dependency maps;
- Prop-level routing surfaces;
- release metadata;
- CI scaffolding.

## Adoption steps

1. Create a branch or small batch dedicated to Mathlib adoption.
2. Update `lakefile.lean` and `lake-manifest.json` using `lake update`.
3. Add the first theorem-level module that needs Mathlib.
4. Run `lake build` locally and in GitHub Actions.
5. Record the adoption in `docs/`.

## Current decision

Mathlib is deferred. The active repository remains minimal Lean until theorem-level concrete modules require it.
