# Current proof status

**Updated:** 2026-09-12 JST  
**Authoritative theorem carrier:** `formal/real-hilbert-uniform-coercive-strong-limit`  
**Authoritative exact canonical theorem SHA:** `015d3cceb59e696f692b6d67e017b3aee4664715`  
**Latest theorem merge:** PR #3887 — `Transport sharp one-link Harnack to continuous physical vacuum`  
**Validated theorem head:** `6b281139612a2c1188f2b6a616b2e1d986fb51c6`  
**Exact-head validation:** PR Lean Fast Check #13589 = completed / success  
**Post-merge validation:** PR Lean Fast Check #13590 = completed / success

## Authority and public surface

The theorem authority remains the branch and exact SHA above. `main` is the public repository surface. When theorem history is mirrored to `main`, the authoritative theorem checkpoint is still identified by the exact canonical theorem SHA rather than by a later documentation or synchronization merge commit.

## Current quantitative checkpoint

The canonical chain now contains:

- the explicit direct ground-state one-link fiber/weight construction;
- exact target-local one-slab Wilson action and kernel factorization;
- the named local Boltzmann factor with `exp (-8 * beta)` / `exp (8 * beta)` pointwise bounds;
- pairwise local-factor Harnack control with factor `exp (16 * beta)`;
- the sharper raw one-slab kernel Harnack comparison with factor `exp (8 * beta)`;
- the RKHS synthesis = raw-kernel integral bridge;
- a pointwise integral eigen-equation for the canonical continuous physical vacuum representative;
- the continuous physical vacuum one-link Harnack comparison with factor `exp (8 * beta)`.

The immediate mathematical frontier is the exact direct ground-state one-link **complete weight** pairwise comparison on its literal carrier, followed by explicit normalization-denominator control, normalized density/minorization, genuine joint one-link conditional-variance control, and globalization to six-color/twelve-spatial coercivity without inverse-volume loss.

## Current claim boundary

This repository does **not** yet contain a completed proof of the Clay Millennium Yang--Mills existence and mass-gap problem.

In particular, the following implications remain invalid unless separately proved:

```text
trivial kernel != quantitative coercivity
fixed-volume strict contraction != scale-uniform spectral gap
unnormalized Harnack != normalized minorization without denominator control
one-link comparison != global Poincare without a globalization theorem
same-root scalar continuum != full 4D continuum Yang--Mills field
```

The scale-uniform target remains a model-derived constant `kappa > 0`, independent of scale, satisfying

```text
kappa * ||x||^2 <= E12,n(R U x)
```

for every scale `n` and every physical `x` in the corresponding top-orthogonal sector. Existing implication machinery then transports such a `kappa` to the six-spatial frame estimate and a positive physical transfer-gap lower bound.
