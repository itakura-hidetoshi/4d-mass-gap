# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

```text
Canonical repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
Development roadmap: ROADMAP.md
```

## Current status - 2026-07-08 JST

This repository is a replayable Lean 4 / mathlib formal-development surface.

The active proof carrier is:

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The latest integrated active-carrier checkpoint is:

```text
PR #675 - Continuous representative package
merge commit 6eebb75d26d4cf139fa65c6557dccebf4be08175
PR head aecb6f1e292d123dffcac9f0c586a30d80e7a3c7
PR Lean Fast Check run 5710 - success
```

The current active draft frontier is:

```text
PR #676 - Spectral representative route
head fbf476daad6df0fac4ea1b3e52d4476a20fdab5c
PR Lean Fast Check run 5711 - in progress when this sync was prepared
```

PR #676 is not an integrated layer until its validation succeeds and it is merged into the active proof carrier.

## Integrated active-carrier layers

The active carrier has moved beyond the completed R4 Hilbert-space handoff, the first mathlib self-adjoint-operator handoff, the R4 adjoint-evaluation layer, and the adjoint-self identity package.

It now includes:

```text
completed R4 Hilbert-space API and handoff;
completed R4 OS semigroup theorem and handoff APIs;
R4 OS generator theorem and handoff APIs;
R4 Hamiltonian theorem and handoff APIs;
R4 self-adjointness input, theorem, handoff, and conclusion layers;
R4 spectral-theorem input, theorem, and handoff interfaces;
actual mathlib LinearPMap / IsSelfAdjoint operator object;
R4 mathlib self-adjoint operator theorem and handoff APIs;
R4 mathlib spectral-theorem input, object, readiness, and invocation-handoff layers;
finite-dimensional mathlib spectral-theorem boundary check;
LinearPMap dense-domain, closedness, graph, graph-to-operator, formal-adjoint, and adjoint-evaluation toolkit layers;
actual R4-operator specialization through adjoint evaluation;
actual R4-operator adjoint-self identity, domain-equality, and graph-equality layers;
bounded-realization, action, inner-product, equality, route, and actual-route packages;
continuous self-adjoint representative package.
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

The latest integrated continuous-representative layer records, from the active bounded-route package, a continuous linear representative `B` of the actual R4 operator with:

```lean
B.toPMap ⊤ = M.mathlibOperator
B.adjoint = B
∀ x y, inner ℝ (B x) y = inner ℝ x (B y)
∀ x, x ∈ M.mathlibOperator.domain
∀ x hx, M.mathlibOperator ⟨x, hx⟩ = B x
```

The main integrated theorem names are:

```lean
r4HilbertMathlibSelfAdjointOperator_unconditional_route_continuous_self_adjoint_representative
r4HilbertMathlibSelfAdjointOperator_unconditional_route_continuous_self_adjoint_action_package
```

These are R4-operator representative consequences on the active formal route.

They are not a spectral-measure construction, a spectral projection family, a positive lower-bound theorem, or a final mass-gap theorem.

## Claim boundary

This repository does **not** yet claim any of the following as completed physical results:

```text
an interacting four-dimensional continuum Yang--Mills theory;
a fully instantiated continuum scaling trajectory;
a physical Yang--Mills Hamiltonian derived from that trajectory;
a spectral measure, functional calculus, or spectral projection family for that physical operator;
a spectral-gap theorem for that physical Hamiltonian;
a positive mass gap derived from uniform physical estimates;
a final public solution of the Yang--Mills mass-gap problem;
independent external mathematical consensus.
```

The current mathlib operator work is still operator-route infrastructure.

The finite-dimensional mathlib spectral-theorem boundary check does **not** apply a spectral theorem to the accumulated R4 `LinearPMap` operator and does **not** construct the physical spectral resolution needed for a mass-gap theorem.

The continuous-representative route is a stronger operator-side bridge, but it still does **not** construct a physical spectral measure, functional calculus, spectral projection family, or positive mass gap.

A theorem that accepts reflection positivity, Euclidean covariance, gauge invariance, compactness, a positive mass slope, a coercive estimate, a self-adjoint operator, a spectral-theorem input, a spectral-resolution object, a bounded-route witness, or a spectral-gap witness as an input remains conditional until those inputs are constructed from the intended physical Yang--Mills approximation family.

## Layer map

```text
finite-volume Wilson / heat-bath theorem generators
  -> conditional OS and operator-limit packages
  -> exact 33/20 internal normalization lane
  -> R4 continuum construction through correlation structure
  -> R4 reflection-positive reconstruction input
  -> R4 quotient, section, range, and transport bookkeeping
  -> completed R4 Hilbert-space API and handoff
  -> completed OS semigroup API and handoff
  -> OS generator API and handoff
  -> Hamiltonian API and handoff
  -> self-adjointness API and conclusion
  -> spectral-theorem input interfaces
  -> mathlib self-adjoint operator object and handoff
  -> mathlib spectral-theorem readiness layers
  -> finite-dimensional mathlib spectral-theorem boundary check
  -> LinearPMap unbounded-operator theorem toolkit
  -> actual R4-operator adjoint infrastructure
  -> bounded-realization and actual-route packages
  -> continuous self-adjoint representative package
  -> spectral representative route
  -> physical spectral theorem application / spectral resolution
  -> physical positive-gap certificate
  -> final theorem and external review
```

Only the layers through the continuous self-adjoint representative package are integrated on the active carrier at this sync point.

The spectral representative route is represented by open Draft PR #676 and is not yet integrated.

## Current theorem boundary

| Surface | Status |
|---|---|
| Finite Wilson Gibbs and finite heat-bath theorem generators | present in the repository history |
| Conditional weak-limit, OS, Hamiltonian, resolvent, and graph-limit packages | present as conditional theorem packages |
| Exact `33/20` scalar lane | internal normalization and audit lane |
| R4 continuum construction through completed Hilbert-space handoff | integrated through PR #600 |
| Completed OS semigroup, OS generator, and Hamiltonian APIs | integrated through PR #615 |
| R4 self-adjointness layers | integrated through PR #622 |
| R4 spectral-theorem input interfaces | integrated through PR #632 as readiness layers |
| Finite-dimensional mathlib spectral-theorem boundary check | integrated by PR #633 |
| LinearPMap unbounded-operator toolkit | integrated through PR #641 |
| Actual R4-operator adjoint-self identity package | integrated by PR #642 |
| Conditional bounded-realization and inner-product packages | integrated through PR #646 |
| Failed bounded-realization rewrite attempt | closed unmerged PR #647; excluded from the integrated carrier |
| Top, equality, graph, action, actual, witness, bounded-route, and actual-route packages | integrated through PR #674 |
| Continuous self-adjoint representative package | integrated by PR #675 |
| Spectral representative route | open Draft PR #676, not integrated at this sync point |
| Physical spectral theorem application to the R4 operator | open |
| Physical positive gap from a concrete continuum scaling family | open |
| Final public theorem and external review | not claimed |

## Replay

Pinned Lean toolchain:

```text
leanprover/lean4:v4.30.0-rc2
```

Pinned mathlib input revision in `lake-manifest.json`:

```text
leanprover-community/mathlib4
rev 5450b53e5ddc75d46418fabb605edbf36bd0beb6
inputRev v4.30.0-rc2
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

The documentation must preserve the distinction between finite-volume theorem generators, conditional continuum packages, internal normalization lanes, R4 reconstruction APIs, mathlib operator handoffs, finite-dimensional spectral-boundary checks, actual R4-operator adjoint infrastructure, bounded-route and continuous-representative packages, physical spectral theorem application, positive-gap layers, and a completed physical Yang--Mills theorem.
