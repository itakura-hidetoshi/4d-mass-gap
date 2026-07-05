# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

```text
Canonical repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
Development roadmap: ROADMAP.md
```

## Current status — 2026-07-06 JST

This repository is a replayable Lean 4 / mathlib formal-development surface.

The active proof carrier is:

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The current integrated R4 Hilbert reconstruction lane has reached a **completed real Hilbert-space API object** and a **completed Hilbert-space handoff API** for downstream OS/operator layers.

The completed carrier is exposed as:

```lean
r4HilbertCompletedHilbertSpace
```

It is identified with the standard mathlib completion of the R4 pre-Hilbert carrier.

The integrated API also exposes:

```text
NormedAddCommGroup
InnerProductSpace ℝ
CompleteSpace
DenseRange from the pre-Hilbert carrier
DenseRange from the quotient carrier
identification with UniformSpace.Completion
quotient-map factorization through the pre-Hilbert carrier
completed Hilbert-space handoff theorem
```

This is a completed Hilbert-space layer for the formal R4 reconstruction route.

It is **not** yet a self-adjoint physical Hamiltonian, a spectral theorem layer for that Hamiltonian, or a four-dimensional Yang--Mills mass-gap theorem.

## Repository snapshot

```text
active proof carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

latest integrated proof checkpoint:
  PR #600 — Add R4 completed Hilbert space handoff API

latest integrated proof checkpoint merge commit:
  4d08c0d0f5be958c223c48c23942f588e4fba8c3

latest integrated proof checkpoint PR head:
  b6a3b450bddfca55549653975f5cfa742f7e97f6

latest integrated validation:
  PR Lean Fast Check run 5626 — success

latest active-carrier documentation sync:
  PR #602 — Update docs after completed Hilbert handoff merge
  merge commit 1bd036596942ec1f60b9b9542c1969dc7a896741

current open draft frontier after that checkpoint:
  none recorded in this README
```

The default branch `main` remains the public repository entry point.

The active proof carrier may be ahead of the older `main` proof surface.

A theorem on the active carrier should not be read as a theorem on `main` until it has been reconciled with `main`, merged, and replayed there.

## Non-claims

The repository does **not** yet establish any of the following as unconditional physical results:

```text
an interacting four-dimensional continuum Yang--Mills theory;
a fully instantiated continuum scaling trajectory;
a physical self-adjoint Yang--Mills Hamiltonian;
a spectral-gap theorem for that Hamiltonian;
an unconditional Clay Millennium Yang--Mills mass-gap theorem;
independent external mathematical consensus.
```

A theorem that accepts reflection positivity, Euclidean covariance, gauge invariance, compactness, a positive mass slope, a coercive estimate, a self-adjoint Hamiltonian, or a spectral-gap witness as an input remains conditional until those inputs are constructed from the intended physical Yang--Mills family.

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

The current active carrier develops an R4 continuum-measure-to-Hilbert reconstruction chain.

The integrated chain now includes the following layers:

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
  -> quotient section and range transport stack
  -> quotient-map injectivity and transport readiness APIs
  -> completion input and completion object data
  -> pre-Hilbert structure data
  -> completed Hilbert structure data
  -> actual dense-range data
  -> standard mathlib completion identity API
  -> quotient-to-standard-completion route
  -> quotient-dense standard completion data
  -> standard real Hilbert completion construction theorem
  -> completed Hilbert space API
  -> completed Hilbert space handoff API
```

As of PR #600, the active carrier has an explicit completed Hilbert-space object and a handoff theorem for downstream layers in the formal R4 reconstruction route.

The central object is:

```lean
r4HilbertCompletedHilbertSpace
```

The main integrated construction theorem is:

```lean
r4HilbertCompletedHilbertSpace_constructed
```

The handoff theorem is:

```lean
r4HilbertCompletedHilbertSpaceHandoff_constructed
```

These package the real inner-product structure, completeness, dense pre-Hilbert map, dense quotient map, equality with the standard `UniformSpace.Completion` of the R4 pre-Hilbert carrier, quotient-map factorization, and route readiness.

The quotient map into the completed space still factors through the pre-Hilbert carrier.

This factorization is part of the integrated API and is not a Hamiltonian statement.

## What is still missing after the completed Hilbert-space handoff

The completed Hilbert-space API and handoff API are important reconstruction milestones.

They do not close the physical mass-gap problem.

The remaining formal and mathematical layers include at least:

```text
OS contraction semigroup on the completed space;
strong continuity of that semigroup;
identification of the generator;
construction of the physical Hamiltonian;
closedness and self-adjointness of the Hamiltonian under explicit hypotheses;
spectral theorem interfaces for that Hamiltonian;
a positive gap statement for the Hamiltonian;
one concrete continuum scaling family supplying all physical hypotheses;
uniform estimates that produce the physical positive gap rather than assume it.
```

## Current theorem boundary

| Surface | Status |
|---|---|
| Finite Wilson Gibbs and finite heat-bath theorem generators | present in the repository history |
| Conditional weak-limit, OS, Hamiltonian, resolvent, and graph-limit packages | present as conditional theorem packages |
| Exact `33/20` scalar lane | internal normalization and audit lane |
| R4 continuum construction through correlation structure | integrated on the active carrier |
| R4 reflection-positive reconstruction input | integrated on the active carrier |
| R4 quotient, section, range, and transport bookkeeping | integrated on the active carrier |
| R4 pre-Hilbert structure data | integrated on the active carrier |
| R4 completed Hilbert structure data | integrated on the active carrier |
| R4 standard completion identity API | integrated on the active carrier |
| R4 quotient-to-standard-completion route | integrated on the active carrier |
| R4 quotient-dense standard completion data | integrated on the active carrier |
| R4 standard real Hilbert completion construction theorem | integrated on the active carrier |
| R4 completed Hilbert space API | integrated by PR #599 |
| R4 completed Hilbert space handoff API | integrated by PR #600 |
| OS semigroup on the completed Hilbert space | open |
| Self-adjoint physical Hamiltonian | open |
| Spectral-gap theorem for the physical Hamiltonian | open |
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

```text
finite-volume Markov or Wilson theorem generators;
conditional continuum reconstruction packages;
exact internal scalar normalization lanes;
active R4 Hilbert reconstruction layers;
completed Hilbert-space API layers;
OS semigroup, Hamiltonian, and spectral-gap layers;
a completed physical Yang--Mills theorem.
```
