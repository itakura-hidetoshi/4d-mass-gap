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

The latest integrated active-carrier checkpoint is:

```text
PR #625 — Add R4 mathlib self-adjoint operator handoff API
merge commit 787983a5fbed818c8de4ddf95d10d9220f816be8
PR head 5cbc220de2a8dcc68101248a05c8615404ce1478
PR Lean Fast Check run 5649 — success
```

The current active draft frontier is:

```text
PR #626 — Add R4 mathlib spectral theorem input layer
head 308b42078499d739dc675d4e434617f13a30f224
PR Lean Fast Check run 5650 — in progress when this sync was prepared
```

PR #626 is not an integrated layer until its validation succeeds and it is merged into the active proof carrier.

## Integrated active-carrier layers

The active carrier has moved beyond the completed R4 Hilbert-space handoff.

It now includes the following integrated API layers:

```text
completed R4 Hilbert-space API;
completed R4 Hilbert-space handoff API;
completed R4 OS semigroup theorem and handoff APIs;
R4 OS generator theorem and handoff APIs;
R4 Hamiltonian theorem and handoff APIs;
R4 self-adjointness input, theorem, handoff, and conclusion layers;
R4 spectral-theorem input, theorem, and handoff interfaces;
actual mathlib LinearPMap / IsSelfAdjoint operator object;
R4 mathlib self-adjoint operator theorem API;
R4 mathlib self-adjoint operator handoff API.
```

The completed Hilbert carrier remains:

```lean
r4HilbertCompletedHilbertSpace
```

The latest integrated handoff theorem is:

```lean
r4HilbertMathlibSelfAdjointOperatorHandoff_constructed
```

The latest integrated layer carries the actual mathlib predicate:

```lean
IsSelfAdjoint M.mathlibOperator
```

together with criterion-level self-adjointness, Hamiltonian-input compatibility, object readiness, handoff readiness, and compatibility with a later spectral-theorem input layer.

## Claim boundary

This repository does **not** yet claim any of the following as unconditional physical results:

```text
an interacting four-dimensional continuum Yang--Mills theory;
a fully instantiated continuum scaling trajectory;
a physical self-adjoint Yang--Mills Hamiltonian derived from that trajectory;
a spectral theorem application producing a physical spectral resolution;
a spectral-gap theorem for that physical Hamiltonian;
a positive mass gap derived from uniform physical estimates;
an unconditional Clay Millennium Yang--Mills mass-gap theorem;
independent external mathematical consensus.
```

The current mathlib self-adjoint operator layer is still a handoff layer.

It does **not** state or invoke the spectral theorem, construct a spectral measure, introduce functional calculus, construct spectral projections, prove a spectral-gap theorem, or derive a physical positive gap from a concrete continuum Yang--Mills scaling family.

A theorem that accepts reflection positivity, Euclidean covariance, gauge invariance, compactness, a positive mass slope, a coercive estimate, a self-adjoint operator, a spectral-theorem input, or a spectral-gap witness as an input remains conditional until those inputs are constructed from the intended physical Yang--Mills family.

## Layer map

```text
finite-volume Wilson / heat-bath theorem generators
  -> conditional OS and operator-limit packages
  -> exact 33/20 internal normalization lane
  -> R4 continuum construction through correlation structure
  -> R4 reflection-positive reconstruction input
  -> R4 quotient, section, range, and transport bookkeeping
  -> R4 pre-Hilbert and completed Hilbert structure data
  -> R4 standard real Hilbert completion theorem
  -> completed Hilbert-space API and handoff
  -> completed OS semigroup API and handoff
  -> OS generator API and handoff
  -> Hamiltonian API and handoff
  -> self-adjointness API and conclusion
  -> spectral-theorem input interfaces
  -> mathlib self-adjoint operator object, theorem API, and handoff
  -> mathlib spectral-theorem input layer
  -> spectral theorem application / spectral resolution
  -> physical positive-gap certificate
  -> final theorem and external review
```

Only the layers through the mathlib self-adjoint operator handoff are integrated on the active carrier at this sync point.

The mathlib spectral-theorem input layer is represented by open Draft PR #626 and is not yet integrated.

## Current theorem boundary

| Surface | Status |
|---|---|
| Finite Wilson Gibbs and finite heat-bath theorem generators | present in the repository history |
| Conditional weak-limit, OS, Hamiltonian, resolvent, and graph-limit packages | present as conditional theorem packages |
| Exact `33/20` scalar lane | internal normalization and audit lane |
| R4 continuum construction through completed Hilbert space handoff | integrated through PR #600 |
| R4 completed OS semigroup theorem and handoff APIs | integrated through PR #606 |
| R4 OS generator theorem and handoff APIs | integrated through PR #611 |
| R4 Hamiltonian theorem and handoff APIs | integrated through PR #615 |
| R4 self-adjointness input, theorem, handoff, and conclusion layers | integrated through PR #622 |
| R4 spectral-theorem input, theorem, and handoff interfaces | integrated through PR #621 as abstract interfaces |
| R4 mathlib self-adjoint operator object | integrated by PR #623 |
| R4 mathlib self-adjoint operator theorem API | integrated by PR #624 |
| R4 mathlib self-adjoint operator handoff API | integrated by PR #625 |
| R4 mathlib spectral-theorem input layer | open Draft PR #626, not integrated at this sync point |
| Physical positive gap from a concrete continuum scaling family | open |
| Unconditional four-dimensional Yang--Mills mass-gap theorem | not claimed |
| Independent external mathematical consensus | not claimed |

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

The documentation must preserve the distinction between finite-volume theorem generators, conditional continuum packages, internal normalization lanes, R4 reconstruction APIs, mathlib operator handoffs, spectral theorem input layers, positive-gap layers, and a completed physical Yang--Mills theorem.
