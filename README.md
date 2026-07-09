# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

```text
Canonical repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
Development roadmap: ROADMAP.md
```

## Current status — 2026-07-09

This repository is a replayable Lean 4 / mathlib formal-development surface.

The active proof carrier is:

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The integrated carrier has moved beyond the completed real Hilbert-space handoff.

The current integrated route now includes:

```text
completed R4 real Hilbert-space API
completed R4 Hilbert-space handoff API
completed R4 OS semigroup handoff API
R4 OS generator input and theorem API
R4 Hamiltonian handoff API
R4 mathlib self-adjoint operator object, theorem API, and handoff API
project-local mathlib graph and adjoint-equality wrappers
actual operator, continuous representative, and inner-action packages
bounded actual operator data and bounded route surfaces
generator, quotient, completed-OS, completed-Hilbert, and completed-pre carrier routes
bare-M bounded actual route and central route supply
enriched bounded/full-domain continuous operator data
direct bare-M bounded-domain package and endpoint family
route-backed boundedness compatibility and migration index
direct boundedness public handoff
```

The current public boundedness route is the **direct bare-`M` bundle**.

Route-backed boundedness names remain as compatibility surfaces, not as the primary construction route.

The current public endpoint names are:

```lean
r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data
r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data
r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package
```

This is still an operator/API and route-supply layer.

It is **not** yet a spectral theorem layer, a spectral projection construction, a numerical mass-gap proof, or an unconditional four-dimensional Yang--Mills mass-gap theorem.

## Repository snapshot

```text
active proof carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

latest integrated carrier PR:
  PR #717 — Direct boundedness public handoff

latest integrated carrier merge commit:
  3d33df3b5c4adae03d0347403022d231d89be219

latest integrated carrier PR head:
  bf6bc9841a9f25c7276ac47bc3b9b158f87e9dcd

latest integrated validation:
  PR Lean Fast Check run 5770 — success

current open draft frontier:
  PR #718 — Complete Yang-Mills direct bounded certificate

current draft frontier validation:
  PR Lean Fast Check run 5771 — in progress at the time this file was updated
```

The default branch `main` remains the public repository entry point.

The active proof carrier may be ahead of the older `main` documentation surface.

A theorem on the active carrier should not be read as a theorem on `main` until it has been reconciled with `main`, merged, and replayed there.

Open or stale draft PRs are not integrated layers unless they are merged into the active proof carrier with a passing PR Lean Fast Check.

## Non-claims

The repository does **not** yet establish any of the following as unconditional physical results:

```text
an interacting four-dimensional continuum Yang--Mills theory;
a fully instantiated continuum scaling trajectory;
a physical positive spectral gap derived from that trajectory;
a spectral projection or functional-calculus construction proving the gap;
an unconditional Clay Millennium Yang--Mills mass-gap theorem;
independent external mathematical consensus.
```

A theorem that accepts reflection positivity, Euclidean covariance, gauge invariance, compactness, a positive mass slope, a coercive estimate, a self-adjoint Hamiltonian, boundedness evidence, a spectral package, or a spectral-gap witness as an input remains conditional until those inputs are constructed from the intended physical Yang--Mills family.

The exact `33/20` lane remains an internal normalization and dependency-routing lane.

It is not an independent physical derivation of the four-dimensional Yang--Mills mass gap.

## Proved and packaged layers

### Finite Wilson and finite heat-bath theory

The earlier finite-volume lane constructs finite Wilson Gibbs probability structures, exact conditional laws, Gibbs Hilbert realizations, heat-bath operators, Dobrushin-type contraction interfaces, Rayleigh and Poincare consequences, and finite Hamiltonian gap consequences from explicit strict finite-volume certificates.

These are finite-volume theorem generators.

They do not by themselves produce a continuum Yang--Mills measure or a physical continuum mass gap.

### Conditional OS and operator-limit theory

The repository contains conditional Osterwalder--Schrader and operator-limit packages.

These packages organize the route from reflection-positive Euclidean data to Hilbert-space, semigroup, Hamiltonian, resolvent, operator-graph, and spectral-interface conclusions under explicit hypotheses.

The conditional packages are useful because they make the remaining physical inputs visible.

They are not a replacement for constructing those inputs.

### R4 Hilbert reconstruction route

The active carrier constructs a formal R4 reconstruction route from continuum-measure and correlation data through quotient bookkeeping into the standard mathlib completion of the R4 pre-Hilbert carrier.

The completed carrier is exposed as:

```lean
r4HilbertCompletedHilbertSpace
```

The completed Hilbert-space handoff API packages the real inner-product structure, completeness, dense pre-Hilbert map, dense quotient map, equality with the standard `UniformSpace.Completion`, quotient-map factorization, and downstream route readiness.

### OS semigroup, generator, and Hamiltonian handoff route

After the completed Hilbert-space handoff, the carrier adds a completed R4 OS semigroup handoff API.

It then adds the R4 OS generator input/theorem surface and the R4 Hamiltonian handoff surface.

These layers expose semigroup laws, contraction, strong continuity, generator graph data, dense-domain and closed-graph obligations, compatibility with the semigroup, Hamiltonian-domain data, nonnegative-form input, symmetry-on-domain input, closability input, and downstream readiness.

They do not by themselves prove a physical spectral gap.

### Mathlib self-adjoint operator route

The carrier now includes an actual mathlib `LinearPMap` self-adjoint operator object for the R4 Hamiltonian route.

It also includes theorem and handoff APIs around the `IsSelfAdjoint` predicate, local wrappers around mathlib graph identities, graph/equality packages, actual operator packages, and inner-action packages.

This is a formal operator-object and API achievement.

It is not a spectral theorem invocation and it is not a spectral-gap theorem.

### Direct bounded actual operator route

The current integrated boundedness route has been normalized around bare `R4HilbertMathlibSelfAdjointOperatorData`.

The direct bare-`M` route now carries bounded actual data, full-domain continuous representative data, a concrete bounded-domain package, the full-domain proof, and the continuous-representative equality in a direct endpoint family.

Route-backed boundedness remains available as a compatibility layer.

The preferred public surface is the direct boundedness public handoff added by PR #717.

## Active construction chain

The active carrier develops the following chain:

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
  -> completed OS semigroup handoff API
  -> OS generator input and theorem API
  -> Hamiltonian handoff API
  -> mathlib self-adjoint operator object/theorem/handoff API
  -> graph, adjoint-equality, actual-operator, and inner-action packages
  -> bounded actual operator data
  -> bounded route surface and route family
  -> unconditional, actual, continuous, and spectral-representative route packages
  -> Hamiltonian-domain, generator-lift, generator-carrier, and completed-carrier routes
  -> quotient-carrier route
  -> bare-M bounded actual route and central route supply
  -> enriched bounded/full-domain continuous operator data
  -> direct bare-M bounded bundle and endpoints
  -> route-backed compatibility and migration index
  -> direct boundedness public handoff
```

The current open draft frontier after this chain is PR #718.

That PR aims to bundle existing construction and direct bounded R4 operator handoff data into a complete Yang--Mills construction certificate surface.

It is not integrated until its check succeeds and it is merged into the active carrier.

## Current theorem boundary

| Surface | Status |
|---|---|
| Finite Wilson Gibbs and finite heat-bath theorem generators | present in the repository history |
| Conditional weak-limit, OS, Hamiltonian, resolvent, and graph-limit packages | present as conditional theorem packages |
| Exact `33/20` scalar lane | internal normalization and audit lane |
| R4 continuum construction through correlation structure | integrated on the active carrier |
| R4 reflection-positive reconstruction input | integrated on the active carrier |
| R4 quotient, section, range, and transport bookkeeping | integrated on the active carrier |
| R4 standard real Hilbert completion construction theorem | integrated on the active carrier |
| R4 completed Hilbert space API | integrated |
| R4 completed Hilbert space handoff API | integrated |
| R4 completed OS semigroup handoff API | integrated by PR #606 |
| R4 OS generator input/theorem API | integrated by PR #608 and PR #610 |
| R4 Hamiltonian handoff API | integrated by PR #615 |
| R4 mathlib self-adjoint operator object/API/handoff | integrated by PR #623, PR #624, and PR #625 |
| Mathlib graph and adjoint-equality wrapper packages | integrated |
| Actual operator and continuous representative packages | integrated |
| Bounded actual operator data and route family | integrated |
| Direct bare-M bounded actual package and endpoints | integrated |
| Direct boundedness public handoff | integrated by PR #717 |
| Complete Yang--Mills direct bounded certificate | open draft frontier in PR #718 |
| Spectral theorem invocation for the physical Hamiltonian | open |
| Spectral projection or functional calculus layer | open |
| Positive spectral-gap theorem for the physical Hamiltonian | open |
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
completed Hilbert-space and OS semigroup API layers;
generator, Hamiltonian, self-adjoint operator, and boundedness route layers;
certificate or handoff surfaces;
spectral theorem and spectral-gap layers;
a completed physical Yang--Mills theorem.
```
