# MGAP4D

**MGAP4D** is Hidetoshi Itakura's Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

```text
Canonical repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
Development roadmap: ROADMAP.md
```

## Current status - 2026-07-07 JST

This repository is a replayable Lean 4 / mathlib formal-development surface.

The active proof carrier is:

```text
formal/real-hilbert-uniform-coercive-strong-limit
```

The latest integrated active-carrier checkpoint is:

```text
PR #641 - Specialize adjoint evaluation to R4 operator
merge commit b55bf22b90c3c357c25ee54224b1c7787ace0db3
PR head 9985976d874ba4c6485eaf4dd552cc27b3561581
PR Lean Fast Check run 5669 - success
```

The current active draft frontier is:

```text
PR #642 - Specialize adjoint-self identities to R4 operator
head 6885ef5654dad36d144fb638d93219193c5e1115
PR Lean Fast Check run 5670 - in progress when this sync was prepared
```

PR #642 is not an integrated layer until its validation succeeds and it is merged into the active proof carrier.

## Integrated active-carrier layers

The active carrier has moved beyond the completed R4 Hilbert-space handoff and beyond the first mathlib self-adjoint-operator handoff.

It now includes the following integrated API and theorem layers:

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
actual R4-operator specializations of that toolkit through adjoint evaluation.
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

The latest integrated R4-operator adjoint-evaluation layer records, among other facts:

```lean
r4HilbertMathlibSelfAdjointOperator_actual_adjoint_apply_of_dense
r4HilbertMathlibSelfAdjointOperator_actual_adjointAux_inner
r4HilbertMathlibSelfAdjointOperator_actual_adjointAux_unique
r4HilbertMathlibSelfAdjointOperator_actual_adjoint_apply_eq
```

These are actual R4 operator consequences for the mathlib `LinearPMap` object, not a spectral-gap theorem.

## Claim boundary

This repository does **not** yet claim any of the following as unconditional physical results:

```text
an interacting four-dimensional continuum Yang--Mills theory;
a fully instantiated continuum scaling trajectory;
a physical self-adjoint Yang--Mills Hamiltonian derived from that trajectory;
a spectral theorem application to the physical R4 Yang--Mills Hamiltonian;
a spectral measure, functional calculus, or spectral projection family for that physical operator;
a spectral-gap theorem for that physical Hamiltonian;
a positive mass gap derived from uniform physical estimates;
an unconditional Clay Millennium Yang--Mills mass-gap theorem;
independent external mathematical consensus.
```

The current mathlib operator work is still unbounded-operator infrastructure.

The repository now contains a finite-dimensional mathlib spectral-theorem boundary check. That boundary check does **not** apply a spectral theorem to the accumulated R4 `LinearPMap` operator and does **not** construct the physical spectral resolution needed for a mass-gap theorem.

A theorem that accepts reflection positivity, Euclidean covariance, gauge invariance, compactness, a positive mass slope, a coercive estimate, a self-adjoint operator, a spectral-theorem input, a spectral-resolution object, or a spectral-gap witness as an input remains conditional until those inputs are constructed from the intended physical Yang--Mills approximation family.

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
  -> mathlib spectral-theorem input / object / invocation readiness layers
  -> finite-dimensional mathlib spectral-theorem boundary check
  -> LinearPMap unbounded-operator theorem toolkit
  -> actual R4-operator specialization through adjoint evaluation
  -> adjoint-self identity package for the actual R4 operator
  -> physical R4 spectral theorem application / spectral resolution
  -> physical positive-gap certificate
  -> final theorem and external review
```

Only the layers through the actual R4-operator adjoint-evaluation layer are integrated on the active carrier at this sync point.

The adjoint-self identity package is represented by open Draft PR #642 and is not yet integrated.

## Current theorem boundary

| Surface | Status |
|---|---|
| Finite Wilson Gibbs and finite heat-bath theorem generators | present in the repository history |
| Conditional weak-limit, OS, Hamiltonian, resolvent, and graph-limit packages | present as conditional theorem packages |
| Exact `33/20` scalar lane | internal normalization and audit lane |
| R4 continuum construction through completed Hilbert-space handoff | integrated through PR #600 |
| R4 completed OS semigroup theorem and handoff APIs | integrated through PR #606 |
| R4 OS generator theorem and handoff APIs | integrated through PR #611 |
| R4 Hamiltonian theorem and handoff APIs | integrated through PR #615 |
| R4 self-adjointness input, theorem, handoff, and conclusion layers | integrated through PR #622 |
| R4 spectral-theorem input, theorem, and handoff interfaces | integrated through PR #621 as abstract interfaces |
| R4 mathlib self-adjoint operator object | integrated by PR #623 |
| R4 mathlib self-adjoint operator theorem API | integrated by PR #624 |
| R4 mathlib self-adjoint operator handoff API | integrated by PR #625 |
| R4 mathlib spectral-theorem input / object / readiness / handoff layers | integrated through PR #632 |
| Finite-dimensional mathlib spectral-theorem boundary check | integrated by PR #633 |
| LinearPMap dense-domain and closedness theorem wrappers | integrated through PR #635 |
| LinearPMap graph and formal-adjoint theorem wrappers | integrated through PR #638 |
| Batched LinearPMap adjoint toolkit | integrated by PR #639 |
| Actual R4-operator specialization of the LinearPMap toolkit | integrated by PR #640 |
| Actual R4-operator adjoint-evaluation layer | integrated by PR #641 |
| Actual R4-operator adjoint-self identity package | open Draft PR #642, not integrated at this sync point |
| Physical spectral theorem application to the R4 operator | open |
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

The documentation must preserve the distinction between finite-volume theorem generators, conditional continuum packages, internal normalization lanes, R4 reconstruction APIs, mathlib operator handoffs, finite-dimensional spectral-boundary checks, actual R4-operator adjoint infrastructure, physical spectral theorem application, positive-gap layers, and a completed physical Yang--Mills theorem.
