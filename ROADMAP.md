# MGAP4D Roadmap

This roadmap records the active proof-development path of `itakura-hidetoshi/4d-mass-gap`.

## Snapshot — 2026-07-06 JST

```text
active proof carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

latest integrated proof checkpoint:
  PR #625 — Add R4 mathlib self-adjoint operator handoff API

latest integrated proof checkpoint merge commit:
  787983a5fbed818c8de4ddf95d10d9220f816be8

latest integrated proof checkpoint PR head:
  5cbc220de2a8dcc68101248a05c8615404ce1478

latest integrated validation:
  PR Lean Fast Check run 5649 — success

current active draft frontier:
  PR #626 — Add R4 mathlib spectral theorem input layer
  head 308b42078499d739dc675d4e434617f13a30f224
  PR Lean Fast Check run 5650 — in progress when this sync was prepared
```

The active carrier now contains a completed R4 Hilbert-space route, a completed OS semigroup route, an OS generator route, Hamiltonian APIs, self-adjointness APIs, and a mathlib `LinearPMap` / `IsSelfAdjoint` operator handoff API.

It still does **not** prove an unconditional interacting four-dimensional continuum Yang--Mills theory, a physical positive mass gap from one fully instantiated continuum scaling family, or a Clay-style final theorem.

Notation:

- `[x]` integrated and replayed on the active proof carrier;
- `[d]` open Draft PR, not integrated;
- `[r]` requires repair, retargeting, or reconciliation;
- `[ ]` not yet constructed or not yet physically instantiated.

A carrier theorem is not a public final theorem.

A draft PR is not an integrated layer.

A conditional theorem package is not a proof that the physical Yang--Mills approximation family supplies its hypotheses.

---

## Milestone 1 — preserve finite Wilson and conditional OS foundations

Status: **available as prior theorem infrastructure**

- [x] finite Wilson Gibbs probability and conditional-law infrastructure;
- [x] finite heat-bath Hilbert and Hamiltonian theorem generators;
- [x] Dobrushin, Rayleigh, Poincare, and finite spectral-gap consequences from strict finite certificates;
- [x] conditional weak-limit, OS reconstruction, Hamiltonian, resolvent, and operator-graph theorem packages;
- [x] exact internal scalar normalization and audit lanes, including the `33/20` lane;
- [x] keep these layers explicitly separated from a final physical mass-gap claim.

Definition of done:

The repository continues to distinguish finite theorem generators, conditional continuum reconstruction packages, internal normalization lanes, and physical theorem claims.

---

## Milestone 2 — maintain the active proof carrier discipline

Status: **active workflow requirement**

- [x] use `formal/real-hilbert-uniform-coercive-strong-limit` as the current proof carrier;
- [x] create one focused branch for each theorem layer;
- [x] open each layer as a Draft PR;
- [x] require PR Lean Fast Check before treating the layer as integrated;
- [x] merge only after fixed-head review;
- [x] start each next layer from the updated carrier head;
- [x] do not promote draft, stale, or failing PR results into README, roadmap, or theorem-boundary language.

Definition of done:

The branch history remains a sequence of small replayable proof layers, and documentation distinguishes merged carrier facts from open draft work.

---

## Milestone 3 — R4 construction spine through correlation data

Status: **integrated on the active carrier**

- [x] complete construction closure;
- [x] R4 gauge-field construction;
- [x] R4 gauge-action construction;
- [x] R4 gauge-invariant construction;
- [x] R4 gauge-invariant Schwinger construction;
- [x] R4 Schwinger n-point family construction;
- [x] R4 correlation functional construction;
- [x] R4 correlation structure construction.

Definition of done:

The R4 continuum-measure construction chain carries the data needed to enter reflection-positive reconstruction inputs without claiming that all physical analytic estimates have been discharged.

---

## Milestone 4 — R4 reflection-positive reconstruction input

Status: **integrated on the active carrier**

- [x] reflection-positive reconstruction input closure;
- [x] propagation of reflection positivity from the measure package;
- [x] propagation of Euclidean invariance from the orbit model;
- [x] propagation of gauge invariance from the orbit model;
- [x] keep the input layer separate from Hilbert-space, Hamiltonian, and spectral-gap claims.

Definition of done:

The reconstruction input surface is available as a formal source of reflection-positive, Euclidean-invariant, and gauge-invariant data for later quotient and Hilbert reconstruction layers.

---

## Milestone 5 — R4 quotient and transport bookkeeping

Status: **integrated on the active carrier**

- [x] Hilbert reconstruction carrier closure;
- [x] equality quotient carrier;
- [x] canonical quotient map;
- [x] quotient projection layer;
- [x] representative-choice layer;
- [x] quotient section layer;
- [x] quotient-section injectivity layer;
- [x] quotient-section range layer;
- [x] quotient-section range uniqueness layer;
- [x] quotient-map injectivity and transport-readiness APIs;
- [x] range-transport pair APIs and round-trip consequences.

Definition of done:

The quotient, section, range, and transport layers provide the bookkeeping needed to route quotient data toward actual analytic structure.

---

## Milestone 6 — completed R4 Hilbert-space route

Status: **integrated through PR #600**

- [x] R4 completion input data;
- [x] R4 completion object data;
- [x] pre-Hilbert structure data;
- [x] completed Hilbert structure data;
- [x] standard completion carrier as `UniformSpace.Completion` of the R4 pre-Hilbert carrier;
- [x] quotient-to-standard-completion route;
- [x] quotient-dense standard completion data;
- [x] completed carrier `r4HilbertCompletedHilbertSpace`;
- [x] completed Hilbert-space theorem API;
- [x] completed Hilbert-space handoff API.

Validation receipts:

```text
PR #599 — Add R4 completed Hilbert space API
  final head 4c9e3b83f46b59e7a9dac9802824ac707f95a8fa
  merge commit a4beaab42037db3f974574c44bfbb114b1c5d934
  PR Lean Fast Check run 5625 — success

PR #600 — Add R4 completed Hilbert space handoff API
  final head b6a3b450bddfca55549653975f5cfa742f7e97f6
  merge commit 4d08c0d0f5be958c223c48c23942f588e4fba8c3
  PR Lean Fast Check run 5626 — success
```

Definition of done:

The active carrier has a completed real Hilbert-space object and a handoff API for downstream OS and operator layers.

---

## Milestone 7 — completed OS semigroup on the completed Hilbert space

Status: **integrated through PR #606**

- [x] completed R4 OS semigroup input data;
- [x] semigroup carrier and time carrier;
- [x] zero time and time addition data;
- [x] semigroup action;
- [x] identity law;
- [x] semigroup law;
- [x] contraction property;
- [x] strong continuity property;
- [x] theorem API;
- [x] handoff API.

Definition of done:

The completed Hilbert space carries an OS semigroup interface with explicit laws, contraction, strong continuity, compatibility, readiness, and a downstream handoff layer.

This remains before the generator, Hamiltonian, spectral theorem application, and spectral-gap layers.

---

## Milestone 8 — OS generator route

Status: **integrated through PR #611**

- [x] infinitesimal-generator input data for the completed R4 OS semigroup;
- [x] generator domain;
- [x] domain-to-Hilbert map;
- [x] generator action;
- [x] dense-domain obligation;
- [x] closed-graph obligation;
- [x] semigroup compatibility;
- [x] dissipative estimate;
- [x] theorem API;
- [x] handoff API.

Definition of done:

The active carrier exposes a generator interface downstream of the completed OS semigroup.

This still does not identify the generator as a physical Hamiltonian, assert self-adjointness, invoke a spectral theorem, or assert a spectral gap.

---

## Milestone 9 — Hamiltonian route

Status: **integrated through PR #615**

- [x] Hamiltonian input data associated with the OS generator handoff;
- [x] Hamiltonian domain;
- [x] map into the generator domain;
- [x] Hamiltonian action;
- [x] compatibility with the generator;
- [x] nonnegative-form input;
- [x] symmetry input;
- [x] theorem API;
- [x] handoff API.

Definition of done:

The active carrier exposes a Hamiltonian API and handoff layer with visible assumptions and compatibility data.

This is not a physical positive-gap result.

---

## Milestone 10 — self-adjointness route

Status: **integrated through PR #622**

- [x] self-adjointness input data downstream of the Hamiltonian handoff;
- [x] operator core;
- [x] core map into the Hamiltonian domain;
- [x] graph-core density input;
- [x] adjoint-domain control input;
- [x] symmetric-closure input;
- [x] deficiency-index vanishing input;
- [x] theorem API;
- [x] handoff API;
- [x] self-adjointness conclusion theorem.

Definition of done:

The active carrier has a replayed self-adjointness conclusion layer under explicit criterion data.

This does not by itself construct a physical spectral gap or a physical continuum scaling family.

---

## Milestone 11 — abstract spectral-theorem interface route

Status: **integrated through PR #621 as an interface layer**

- [x] spectral-theorem input data downstream of the self-adjointness handoff;
- [x] spectral parameters;
- [x] abstract projection-family data;
- [x] spectral-resolution input;
- [x] functional-calculus input;
- [x] theorem API;
- [x] handoff API.

Definition of done:

The active carrier can route data toward a later spectral-theorem layer while keeping spectral resolution, functional calculus, and gap statements separated from the self-adjointness route.

This interface layer is not yet a mathlib spectral theorem application and not a spectral-gap theorem.

---

## Milestone 12 — mathlib self-adjoint operator object and handoff

Status: **integrated through PR #625**

- [x] construct an actual mathlib operator object using `LinearPMap` on the completed R4 Hilbert carrier;
- [x] carry the actual mathlib predicate `IsSelfAdjoint M.mathlibOperator`;
- [x] bundle compatibility with the Hamiltonian input;
- [x] expose theorem-facing projections;
- [x] expose handoff readiness;
- [x] expose compatibility with a later spectral-theorem input layer;
- [x] keep this layer separate from spectral theorem invocation, spectral projections, functional calculus, and gap claims.

Validation receipt:

```text
PR #625 — Add R4 mathlib self-adjoint operator handoff API
  final head 5cbc220de2a8dcc68101248a05c8615404ce1478
  merge commit 787983a5fbed818c8de4ddf95d10d9220f816be8
  PR Lean Fast Check run 5649 — success
```

Definition of done:

The active carrier exposes a mathlib self-adjoint operator object and a stable handoff API for the next spectral-theorem input layer.

---

## Milestone 13 — mathlib spectral-theorem input layer

Status: **open Draft PR #626**

- [d] carry the actual mathlib `LinearPMap` / `IsSelfAdjoint` operator object into a spectral-theorem input package;
- [d] avoid stating or invoking the spectral theorem in this layer;
- [d] avoid constructing spectral measure, functional calculus, or spectral projections in this layer;
- [d] avoid spectral-gap and positive-lower-bound claims in this layer;
- [d] wait for PR Lean Fast Check and fixed-head integration before marking the layer as integrated.

Current draft receipt:

```text
PR #626 — Add R4 mathlib spectral theorem input layer
  head 308b42078499d739dc675d4e434617f13a30f224
  PR Lean Fast Check run 5650 — in progress when this sync was prepared
```

Definition of done:

A replayed mathlib spectral-theorem input layer exists on the active carrier and is cleanly separated from actual spectral theorem invocation and spectral-gap assertions.

---

## Milestone 14 — spectral theorem application and spectral resolution

Status: **open**

- [ ] instantiate the chosen mathlib spectral theorem route;
- [ ] construct or expose the relevant spectral measure or spectral projection family;
- [ ] connect the spectral-resolution layer to the mathlib self-adjoint operator handoff;
- [ ] add functional-calculus interfaces only if required by the chosen route;
- [ ] keep this layer separate from a positive-gap lower-bound claim.

Definition of done:

The active carrier has a replayed spectral theorem application or spectral-resolution layer for the relevant self-adjoint operator.

---

## Milestone 15 — physical positive-gap certificate

Status: **decisive open mathematical frontier**

- [ ] specify one concrete continuum scaling family;
- [ ] define its gauge group, lattice family, boundary conditions, observable sector, and interpolation maps;
- [ ] prove tightness or compactness estimates for that family;
- [ ] prove nontriviality of the resulting continuum limit;
- [ ] prove a uniform positive gap, mass slope, Poincare/log-Sobolev estimate, transfer contraction, or equivalent physical certificate;
- [ ] show that the certificate feeds the completed Hamiltonian / spectral-gap interface.

Definition of done:

A positive mass-gap lower bound is derived from the actual physical approximation family rather than supplied as an abstract input.

---

## Milestone 16 — final theorem and external review

Status: **not claimed**

- [ ] assemble a single replayable final theorem path;
- [ ] remove or discharge all nonphysical placeholders;
- [ ] document every remaining hypothesis and every theorem dependency;
- [ ] pass internal review gates;
- [ ] obtain independent external mathematical review;
- [ ] only then consider public final theorem language.

Definition of done:

The repository can state a final theorem without conflating finite-volume results, conditional transfer theorems, internal normalization lanes, completed Hilbert-space work, operator handoff APIs, spectral theorem input layers, and the actual four-dimensional Yang--Mills mass-gap theorem.
