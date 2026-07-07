# MGAP4D Roadmap

This roadmap records the active proof-development path of `itakura-hidetoshi/4d-mass-gap`.

## Snapshot - 2026-07-08 JST

```text
active proof carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

latest integrated proof checkpoint:
  PR #675 - Continuous representative package

latest integrated proof checkpoint merge commit:
  6eebb75d26d4cf139fa65c6557dccebf4be08175

latest integrated proof checkpoint PR head:
  aecb6f1e292d123dffcac9f0c586a30d80e7a3c7

latest integrated validation:
  PR Lean Fast Check run 5710 - success

current active draft frontier:
  PR #676 - Spectral representative route
  head fbf476daad6df0fac4ea1b3e52d4476a20fdab5c
  PR Lean Fast Check run 5711 - in progress when this sync was prepared
```

The active carrier now contains a completed R4 Hilbert-space route, a completed OS semigroup route, an OS generator route, Hamiltonian APIs, self-adjointness APIs, a mathlib `LinearPMap` / `IsSelfAdjoint` operator object, mathlib spectral-theorem readiness and boundary layers, a LinearPMap unbounded-operator theorem toolkit, actual R4-operator adjoint infrastructure, bounded-realization and actual-route packages, and a continuous self-adjoint representative package.

It still does **not** prove a completed interacting four-dimensional continuum Yang--Mills theory, a physical spectral resolution for the R4 Yang--Mills Hamiltonian, a physical positive mass gap from one fully instantiated continuum scaling family, or a final public theorem.

Notation:

- `[x]` integrated and replayed on the active proof carrier;
- `[d]` open Draft PR, not integrated;
- `[r]` requires repair, retargeting, or reconciliation;
- `[ ]` not yet constructed or not yet physically instantiated.

A carrier theorem is not a public final theorem.

A draft PR is not an integrated layer.

A finite-dimensional mathlib spectral-theorem boundary check is not a physical R4 spectral theorem application.

A bounded-route or representative package is not a positive mass-gap certificate.

A conditional theorem package is not a proof that the physical Yang--Mills approximation family supplies its hypotheses.

---

## Milestone 1 - preserve finite Wilson and conditional OS foundations

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

## Milestone 2 - maintain the active proof carrier discipline

Status: **active workflow requirement**

- [x] use `formal/real-hilbert-uniform-coercive-strong-limit` as the current proof carrier;
- [x] create one focused branch for each theorem layer;
- [x] open each layer as a Draft PR;
- [x] require PR Lean Fast Check before treating the layer as integrated;
- [x] merge only after fixed-head review;
- [x] start each next layer from the updated carrier head;
- [x] do not promote draft, stale, closed-unmerged, or failing PR results into README, roadmap, or theorem-boundary language.

Definition of done:

The branch history remains a sequence of small replayable proof layers, and documentation distinguishes merged carrier facts from open draft work.

---

## Milestone 3 - R4 reconstruction spine through completed Hilbert space

Status: **integrated through PR #600**

- [x] complete construction closure;
- [x] R4 gauge-field construction;
- [x] R4 gauge-action construction;
- [x] R4 gauge-invariant construction;
- [x] R4 gauge-invariant Schwinger construction;
- [x] R4 Schwinger n-point family construction;
- [x] R4 correlation functional construction;
- [x] R4 correlation structure construction;
- [x] reflection-positive reconstruction input closure;
- [x] quotient, section, range, and transport bookkeeping;
- [x] completed carrier `r4HilbertCompletedHilbertSpace`;
- [x] completed Hilbert-space theorem API;
- [x] completed Hilbert-space handoff API.

Definition of done:

The R4 reconstruction route carries a completed real Hilbert-space object and a handoff API for downstream OS and operator layers, without claiming that all physical analytic estimates have been discharged.

---

## Milestone 4 - OS semigroup, generator, and Hamiltonian route

Status: **integrated through PR #615**

- [x] completed R4 OS semigroup input data;
- [x] semigroup action, identity law, semigroup law, contraction, and strong continuity;
- [x] OS semigroup theorem API and handoff API;
- [x] infinitesimal-generator input data;
- [x] generator domain, domain-to-Hilbert map, generator action, dense-domain input, closed-graph input, semigroup compatibility, and dissipative estimate;
- [x] generator theorem API and handoff API;
- [x] Hamiltonian domain, action, generator compatibility, nonnegative-form input, symmetry input, theorem API, and handoff API.

Definition of done:

The active carrier exposes OS semigroup, generator, and Hamiltonian APIs with visible assumptions and compatibility data.

This is not a physical positive-gap result.

---

## Milestone 5 - self-adjointness route

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

## Milestone 6 - mathlib operator and spectral-readiness route

Status: **integrated through PR #633**

- [x] construct an actual mathlib operator object using `LinearPMap` on the completed R4 Hilbert carrier;
- [x] carry the actual mathlib predicate `IsSelfAdjoint M.mathlibOperator`;
- [x] expose mathlib self-adjoint operator theorem and handoff APIs;
- [x] expose spectral-theorem input, object, readiness, invocation-input, invocation-readiness, and invocation-handoff layers;
- [x] add a finite-dimensional mathlib spectral-theorem boundary check;
- [x] keep the finite-dimensional boundary check separate from the R4 physical spectral-resolution layer.

Validation receipts:

```text
PR #623 - Add R4 mathlib self-adjoint operator data
PR #624 - Add R4 mathlib self-adjoint operator theorem API
PR #625 - Add R4 mathlib self-adjoint operator handoff API
PR #626 - Add R4 mathlib spectral theorem input layer
PR #628 - Add R4 mathlib spectral theorem object API
PR #629 - Add R4 mathlib spectral theorem object handoff
PR #630 - Add R4 mathlib spectral theorem invocation input
PR #631 - Add R4 mathlib spectral theorem invocation readiness API
PR #632 - Add R4 mathlib spectral theorem invocation handoff
PR #633 - Add finite-dimensional mathlib spectral theorem boundary check
```

Definition of done:

The active carrier has a stable mathlib operator object and spectral-readiness interfaces, while keeping actual physical R4 spectral theorem invocation and spectral-gap assertions deferred.

---

## Milestone 7 - LinearPMap unbounded-operator toolkit

Status: **integrated through PR #641**

- [x] invoke dense-domain facts for self-adjoint `LinearPMap`s;
- [x] invoke closedness of a self-adjoint `LinearPMap`;
- [x] invoke graph identities for self-adjoint `LinearPMap`s;
- [x] invoke the graph-to-operator theorem for adjoints;
- [x] invoke formal-adjoint theorem wrappers;
- [x] batch dense-domain, closedness, graph, graph-to-operator, formal-adjoint, and adjoint-evaluation support;
- [x] specialize the toolkit to the actual R4 operator `M.mathlibOperator`;
- [x] record the actual dense-domain adjoint application formula;
- [x] record the actual `adjointAux` inner-product identity;
- [x] record uniqueness of `adjointAux`;
- [x] record the actual adjoint application equality criterion.

Validation receipts:

```text
PR #634 - Invoke LinearPMap dense domain theorem
PR #635 - Invoke LinearPMap self-adjoint closedness theorem
PR #636 - Invoke LinearPMap self-adjoint graph theorem
PR #637 - Invoke LinearPMap graph-to-operator theorem
PR #638 - Invoke LinearPMap formal-adjoint theorem
PR #639 - Add batched LinearPMap adjoint toolkit
PR #640 - Specialize LinearPMap toolkit to R4 operator
PR #641 - Specialize adjoint evaluation to R4 operator
```

Definition of done:

Pinned-mathlib `LinearPMap` facts needed by the R4 operator route are available through project-local wrappers and bundled theorem packages.

---

## Milestone 8 - actual R4-operator adjoint-self identities

Status: **integrated by PR #642**

- [x] prove `LinearPMap.adjoint M.mathlibOperator = M.mathlibOperator`;
- [x] prove the reverse equality;
- [x] prove equality of adjoint domain and original domain;
- [x] prove equality of adjoint graph and original graph;
- [x] bundle adjoint equality, domain equality, graph equality, and the previous adjoint-evaluation formula.

Validation receipt:

```text
PR #642 - Specialize adjoint-self identities to R4 operator
  final head 6885ef5654dad36d144fb638d93219193c5e1115
  merge commit f4ec236d8fe0fa4c7e005dd0acb5a43b4eb08a47
```

Definition of done:

The actual R4 mathlib operator carries the adjoint-equals-self, domain-equality, and graph-equality package on the active carrier.

---

## Milestone 9 - bounded-realization, action, and route packages

Status: **integrated through PR #674**

- [x] build conditional bounded-realization data;
- [x] record domain and action formulas for bounded representatives;
- [x] record inner-product formulas;
- [x] keep the failed PR #647 excluded from the integrated carrier;
- [x] rebuild the route through top, equality, graph, action, actual, witness, and continuous packages;
- [x] add bounded realization discharge bridge;
- [x] add bounded actual operator data;
- [x] add bounded construction route data and package;
- [x] add bounded route family;
- [x] add bounded-route package;
- [x] add actual route package.

Representative validation receipts:

```text
PR #646 - Add bounded realization inner formula for R4 operator
PR #647 - Add bounded realization self-adjoint consequence - closed unmerged, excluded
PR #648 - Top consequence
PR #649 - Top actual equality
PR #650 - Adjoint equality
PR #651 - Inner symmetry
PR #652 - Self-adjoint package
PR #653 - Existence package
PR #654 - Domain package
PR #655 - Action package
PR #656 - Inner action package
PR #657 - Graph package
PR #658 - Operator equality package
PR #659 - Actual self-adjoint package
PR #660 - Actual toolkit package
PR #661 - Top witness package
PR #662 - Top witness actual toolkit package
PR #663 - Continuous witness package
PR #664 - Continuous representative package
PR #665 - Continuous representative actual package
PR #666 - Bounded realization discharge bridge
PR #667 - Bounded actual operator data
PR #668 - Bounded route surface
PR #669 - Full domain data
PR #670 - Bounded construction route data
PR #671 - Bounded construction route package
PR #672 - Bounded route family
PR #673 - Unconditional bounded route package
PR #674 - Actual route package
```

Definition of done:

The active carrier has a replayed route from bounded-representative data to actual R4-operator action and equality packages, with the failed closed PR explicitly excluded.

This remains operator-route infrastructure, not a positive mass-gap certificate.

---

## Milestone 10 - continuous self-adjoint representative package

Status: **integrated by PR #675**

- [x] extract a continuous representative of the actual R4 operator from the active bounded-route package;
- [x] prove `B.toPMap ⊤ = M.mathlibOperator`;
- [x] prove `B.adjoint = B`;
- [x] prove the continuous inner-product symmetry formula;
- [x] retain the actual-domain membership formula;
- [x] retain the actual-operator action formula;
- [x] retain the inner-product action formula for later spectral-measure and functional-calculus routing.

Validation receipt:

```text
PR #675 - Continuous representative package
  final head aecb6f1e292d123dffcac9f0c586a30d80e7a3c7
  merge commit 6eebb75d26d4cf139fa65c6557dccebf4be08175
  PR Lean Fast Check run 5710 - success
```

Main theorem names:

```lean
r4HilbertMathlibSelfAdjointOperator_unconditional_route_continuous_self_adjoint_representative
r4HilbertMathlibSelfAdjointOperator_unconditional_route_continuous_self_adjoint_action_package
```

Definition of done:

The active carrier exposes a continuous self-adjoint representative package for the actual R4 operator route.

This still does not construct a physical spectral measure, spectral projection family, functional calculus, positive lower bound, or mass-gap theorem.

---

## Milestone 11 - spectral representative route

Status: **open Draft PR #676**

- [d] combine the spectral-theorem invocation input layer with the continuous self-adjoint representative;
- [d] keep invocation readiness, invocation deferral, spectral-measure deferral, and spectral-gap deferral explicit;
- [d] retain the continuous representative and action formulas for later spectral routing;
- [d] wait for PR Lean Fast Check and fixed-head integration before marking the layer as integrated.

Current draft receipt:

```text
PR #676 - Spectral representative route
  head fbf476daad6df0fac4ea1b3e52d4476a20fdab5c
  PR Lean Fast Check run 5711 - in progress when this sync was prepared
```

Definition of done:

The spectral invocation input route and the continuous representative package are available together on the active carrier, while spectral measure, functional calculus, spectral projection, and gap assertions remain deferred.

---

## Milestone 12 - physical R4 spectral theorem application and spectral resolution

Status: **open**

- [ ] choose or build the appropriate mathlib route for the relevant R4 operator surface;
- [ ] instantiate that route for the active R4 operator or its accepted representative route;
- [ ] construct or expose the relevant spectral measure or spectral projection family;
- [ ] connect the spectral-resolution layer to the actual R4 operator infrastructure;
- [ ] add functional-calculus interfaces only if required by the chosen route;
- [ ] keep this layer separate from a positive-gap lower-bound claim.

Definition of done:

The active carrier has a replayed spectral theorem application or spectral-resolution layer for the actual R4 operator route.

---

## Milestone 13 - physical positive-gap certificate

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

## Milestone 14 - final theorem and external review

Status: **not claimed**

- [ ] assemble a single replayable final theorem path;
- [ ] remove or discharge all nonphysical placeholders;
- [ ] document every remaining hypothesis and every theorem dependency;
- [ ] pass internal review gates;
- [ ] obtain independent external mathematical review;
- [ ] only then consider final public theorem language.

Definition of done:

The repository can state a final theorem without conflating finite-volume results, conditional transfer theorems, internal normalization lanes, completed Hilbert-space work, operator handoff APIs, finite-dimensional spectral-boundary checks, actual R4-operator adjoint infrastructure, bounded-route and continuous-representative packages, physical spectral theorem application, positive-gap layers, and the actual four-dimensional Yang--Mills mass-gap theorem.
