# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

```text
Canonical repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
Development roadmap: ROADMAP.md
```

## Current status — 2026-07-09 JST

This repository is a replayable Lean 4 / mathlib formal-development surface.

The active proof carrier is:

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The latest integrated theorem/certificate checkpoint on the active carrier is:

```text
PR #718 — Complete Yang-Mills direct bounded certificate
merge commit dd137504ecea43c97097151de5689c41b2121703
PR head abe7194274aec8c4e277bcc5165c2156d66b53f8
PR Lean Fast Check run 5772 — success
```

The active carrier is currently centered on a direct bounded R4 operator route.

The preferred boundedness surface is the **direct bare-`M` bundle**.

Route-backed boundedness names remain available only as compatibility surfaces.

The newest integrated certificate layer bundles two already-installed surfaces:

```text
Euclidean Yang-Mills finite-volume / continuum construction certificate
  + direct bounded R4 operator public handoff
  -> complete Yang-Mills direct bounded certificate surface
```

This is still a formal construction-certificate and operator-handoff layer.

It is **not** a new spectral theorem invocation, not a new spectral projection construction, not a numerical mass-gap proof, and not an unconditional four-dimensional Yang--Mills mass-gap theorem.

## Current public endpoints

The preferred direct boundedness endpoints remain:

```lean
r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data
r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data
r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package
```

The complete construction certificate layer exposes:

```lean
EuclideanYangMillsCompleteConstructionDirectBoundedCertificate

euclideanYangMillsCompleteConstructionDirectBoundedCertificate

euclidean_yang_mills_complete_construction_direct_bounded_full_spectral_package

euclidean_yang_mills_complete_construction_direct_bounded_public_handoff

euclidean_yang_mills_complete_construction_direct_bounded_package
```

The public handoff marker records:

```text
primary bounded route: bare-M-direct-bundle
route-backed role: compatibility-only
public handoff status: direct-bare-M-primary-route-backed-compatibility
```

## Non-claims

The repository does **not** yet establish any of the following as unconditional physical results:

```text
an independently completed interacting four-dimensional continuum Yang-Mills theory;
a fully instantiated continuum scaling trajectory with all analytic estimates discharged;
a physical spectral theorem application derived from that concrete trajectory;
a newly constructed physical spectral projection family proving a gap;
a positive lower bound derived from a uniform physical estimate;
an unconditional Clay Millennium Yang-Mills mass-gap theorem;
independent external mathematical consensus.
```

The complete construction certificate imports and packages the existing construction-spine spectral certificate.

That packaging is not a substitute for proving that one concrete physical Yang-Mills approximation family supplies every required continuum, spectral, and positive-gap input.

A theorem that accepts reflection positivity, Euclidean covariance, gauge invariance, compactness, a positive mass slope, a coercive estimate, a self-adjoint Hamiltonian, boundedness evidence, a spectral package, a PVM field, or a spectral-gap witness as an input remains conditional until those inputs are constructed from the intended physical Yang-Mills family.

The exact `33/20` lane remains an internal normalization and dependency-routing lane.

It is not an independent physical derivation of the four-dimensional Yang-Mills mass gap.

## Integrated active-carrier route

The active carrier now includes:

```text
finite Wilson and heat-bath theorem-generator infrastructure
conditional OS, Hamiltonian, resolvent, graph-limit, and spectral-interface packages
exact 33/20 internal normalization lane
R4 continuum-measure construction spine
R4 gauge-field, gauge-action, gauge-invariant, Schwinger, correlation, and reconstruction-input layers
R4 quotient, section, range, and transport bookkeeping
R4 standard real Hilbert completion construction theorem
completed R4 real Hilbert-space API and handoff API
completed R4 OS semigroup handoff API
R4 OS generator input and theorem API
R4 Hamiltonian handoff API
R4 mathlib self-adjoint LinearPMap operator object, theorem API, and handoff API
project-local mathlib graph and adjoint-equality wrappers
actual operator, graph, equality, continuous-representative, and inner-action packages
bounded actual operator data and bounded route family
generator, quotient, completed-OS, completed-Hilbert, and completed-pre carrier routes
bare-M bounded actual route and central route supply
enriched bounded/full-domain continuous operator data
direct bare-M bounded-domain package, bundle, and endpoint family
route-backed boundedness compatibility and migration index
direct boundedness public handoff
complete Yang-Mills direct bounded certificate surface
```

The completed Hilbert carrier remains:

```lean
r4HilbertCompletedHilbertSpace
```

The actual mathlib operator object remains:

```lean
M.mathlibOperator
```

The integrated self-adjoint predicate remains:

```lean
IsSelfAdjoint M.mathlibOperator
```

## Active construction chain

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
  -> complete Yang-Mills direct bounded certificate
```

## Current theorem boundary

| Surface | Status |
|---|---|
| Finite Wilson Gibbs and finite heat-bath theorem generators | present in repository history |
| Conditional weak-limit, OS, Hamiltonian, resolvent, graph-limit, and spectral-interface packages | present as conditional theorem packages |
| Exact `33/20` scalar lane | internal normalization and audit lane |
| R4 continuum construction through correlation structure | integrated on the active carrier |
| R4 reflection-positive reconstruction input | integrated on the active carrier |
| R4 quotient, section, range, and transport bookkeeping | integrated on the active carrier |
| R4 standard real Hilbert completion construction theorem | integrated on the active carrier |
| R4 completed Hilbert space API and handoff API | integrated |
| R4 completed OS semigroup handoff API | integrated by PR #606 |
| R4 OS generator input/theorem API | integrated by PR #608 and PR #610 |
| R4 Hamiltonian handoff API | integrated by PR #615 |
| R4 mathlib self-adjoint operator object/API/handoff | integrated by PR #623, PR #624, and PR #625 |
| Mathlib graph, adjoint-equality, actual-operator, and inner-action packages | integrated |
| Bounded actual operator data and route family | integrated |
| Direct bare-M bounded actual package, bundle, and endpoints | integrated |
| Direct boundedness public handoff | integrated by PR #717 |
| Complete Yang-Mills direct bounded certificate | integrated by PR #718 |
| Spectral theorem invocation for the physical Hamiltonian | open |
| New physical spectral projection or functional-calculus layer | open |
| Positive spectral-gap theorem for the physical Hamiltonian | open |
| Uniform physical positive gap from a concrete continuum scaling family | open |
| Unconditional four-dimensional Yang-Mills mass-gap theorem | not claimed |
| Independent external mathematical consensus | not claimed |

Legacy or stale open PRs are not active-carrier facts unless they are reconciled, checked, and merged into the active proof carrier.

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

For current carrier work, read the PR base, head SHA, and CI status before treating a theorem layer as integrated.

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
construction certificate and public handoff surfaces;
spectral theorem and spectral-gap layers;
a completed physical Yang-Mills theorem.
```
