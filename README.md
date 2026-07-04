# MGAP4D

**MGAP4D** is Hidetoshi Itakura's canonical Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

```text
Canonical repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
Development roadmap: ROADMAP.md
```

## Current status — 2026-07-05

This repository is a replayable Lean 4 / mathlib formal-development surface.

It does **not** yet establish an unconditional interacting four-dimensional continuum Yang--Mills theory, a complete physical Hilbert-space reconstruction, a self-adjoint physical Hamiltonian, or a physical mass gap derived from one fully instantiated continuum scaling trajectory.

The active mathematical work is being carried on the branch:

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The default branch `main` remains the public repository entry point, but the current proof carrier has advanced far beyond the older `main` documentation surface.

A theorem on the active carrier should not be read as a theorem on `main` until it has been reconciled with `main`, merged, and replayed there.

A theorem that accepts reflection positivity, Euclidean covariance, gauge invariance, compactness, a positive mass slope, a coercive estimate, a self-adjoint Hamiltonian, or a spectral-gap witness as an input remains conditional until those inputs are constructed from the intended physical Yang--Mills family.

## Repository snapshot

```text
active proof carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

latest integrated carrier PR:
  PR #539 — Add R4 Hilbert reconstruction quotient section range uniqueness layer

latest integrated carrier merge commit:
  1364ddc7f57a98a49482d81ec474e152d962ccee

latest integrated carrier PR head:
  0de760e4b70749942aac5e61efb189143e6e315a

latest integrated validation:
  PR Lean Fast Check run 5554 — success

current open draft after that checkpoint:
  PR #540 — Add R4 Hilbert reconstruction quotient map injectivity layer
  head da05bf98e9c3f87f3d363e189c6a91d45d5ec7ae
  PR Lean Fast Check run 5555 — failure
```

PR #540 is therefore documented as an open draft frontier, not as an integrated theorem layer.

## Proved and packaged layers

### Finite Wilson and finite heat-bath theory

The earlier finite-volume lane constructs finite Wilson Gibbs probability structures, exact conditional laws, Gibbs Hilbert realizations, heat-bath operators, Dobrushin-type contraction interfaces, Rayleigh and Poincare consequences, and finite Hamiltonian gap consequences from explicit strict finite-volume certificates.

These are finite-volume theorem generators.

They do not by themselves produce a continuum Yang--Mills measure or a physical continuum mass gap.

### Conditional OS and operator-limit theory

The repository contains conditional Osterwalder--Schrader and operator-limit packages.

These packages organize the route from reflection-positive Euclidean data to Hilbert-space, semigroup, Hamiltonian, resolvent, and operator-graph conclusions under explicit hypotheses.

The conditional packages are useful because they make the remaining physical inputs visible.

They are not a replacement for constructing those inputs.

### Exact `33/20` normalization lane

The repository transports the normalized scalar value `33/20` through internal Hamiltonian, spectral, and audit interfaces.

This is an internal normalization and dependency-routing lane.

It is not an independent derivation of the physical four-dimensional Yang--Mills mass gap, and it is not automatically identified with the conditional Wilson/OS mass parameter.

See `docs/exact_gap_layer_separation.md` where applicable.

## Active R4 construction chain

The current active carrier is developing an R4 continuum-measure-to-Hilbert reconstruction chain.

The integrated chain includes the following layers:

```text
EuclideanYangMillsContinuumMeasureConstructionSpine
  -> EuclideanYangMillsCompleteConstructionClosure
  -> R4 gauge-field construction
  -> R4 gauge-action construction
  -> R4 gauge-invariant construction
  -> R4 gauge-invariant Schwinger construction
  -> R4 Schwinger n-point family
  -> R4 correlation functional
  -> R4 correlation structure
  -> R4 reflection-positive reconstruction input
  -> R4 Hilbert reconstruction carrier
  -> equality quotient carrier
  -> quotient projection
  -> quotient representative choice
  -> quotient section
  -> quotient-section injectivity
  -> quotient-section range
  -> quotient-section range uniqueness
```

As of PR #539, the carrier proves the quotient-section range uniqueness layer.

The bundled outputs include:

```text
witness uniqueness inside the quotient-section range
projection uniqueness for selected representatives
full witness uniqueness
Function.Injective quotientSection
reflection positivity carried from the measure package
Euclidean invariance carried from the orbit model
gauge invariance carried from the orbit model
```

This is an important algebraic separation step for the reconstruction route.

It is still not the completed physical Hilbert space.

## What is still missing for the completed Hilbert space

The present quotient and section layers organize representatives and equality data.

A completed physical Hilbert reconstruction still requires additional formal layers, including at least:

- a well-defined norm or seminorm on the quotient carrier;
- a well-defined inner product or bilinear form on quotient classes;
- proof that quotient representatives do not change the norm and inner product;
- positivity and null-space consistency;
- additive and scalar algebraic structure on the quotient;
- normed-space and inner-product-space instances;
- Cauchy completion or a complete carrier;
- a `CompleteSpace` and Hilbert-space instance;
- a dense physical-state map from the observable input surface;
- the OS contraction semigroup on the reconstructed space;
- the physical Hamiltonian as a closed self-adjoint generator;
- spectral theorem interfaces and a gap statement for the physical Hamiltonian.

PR #540 begins the next equality-reflection step by attempting to prove injectivity of the current quotient map.

Because PR #540 is still draft and its current CI run failed, that result is not counted as integrated.

## Current theorem boundary

| Surface | Status |
|---|---|
| Finite Wilson Gibbs and finite heat-bath theorem generators | present in the repository history |
| Conditional weak-limit, OS, Hamiltonian, resolvent, and graph-limit packages | present as conditional theorem packages |
| Exact `33/20` scalar lane | internal normalization and audit lane |
| R4 continuum construction closure through correlation structure | integrated on the active carrier |
| R4 reflection-positive reconstruction input | integrated on the active carrier |
| R4 Hilbert reconstruction carrier | integrated on the active carrier |
| R4 quotient projection, representative, and section layers | integrated on the active carrier |
| R4 quotient-section range uniqueness | integrated by PR #539 |
| R4 quotient-map injectivity | draft PR #540; not integrated |
| Completed physical Hilbert space | open |
| Self-adjoint physical Hamiltonian from the completed Hilbert space | open |
| Uniform physical positive gap from a concrete continuum scaling family | open |
| Unconditional four-dimensional Yang--Mills mass-gap theorem | not claimed |
| Independent external mathematical consensus | not claimed |

## Replay

Pinned Lean toolchain:

```text
leanprover/lean4:v4.30.0-rc2
```

From a fresh clone:

```bash
lake update
lake build
```

The repository also uses PR-level Lean fast checks for each focused proof layer.

For current carrier work, read the PR base and CI status before treating a theorem layer as integrated.

## Development discipline

New theorem layers should remain small, replayable, and reviewable.

The active workflow is:

```text
create a focused branch
open a Draft PR
do not treat the layer as integrated until PR Lean Fast Check succeeds
merge into formal/real-hilbert-uniform-coercive-strong-limit after fixed-head review
then start the next layer from the updated carrier head
```

The documentation must preserve the distinction between:

- finite-volume Markov or Wilson theorem generators;
- conditional continuum reconstruction packages;
- exact internal scalar normalization lanes;
- active R4 Hilbert reconstruction layers;
- a completed physical Yang--Mills theorem.
