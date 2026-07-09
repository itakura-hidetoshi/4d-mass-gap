# MGAP4D Roadmap

This roadmap records the active proof-development path of `itakura-hidetoshi/4d-mass-gap`.

## Snapshot — 2026-07-09 JST

```text
active proof carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

latest integrated theorem/certificate checkpoint:
  PR #718 — Complete Yang-Mills direct bounded certificate

latest integrated checkpoint merge commit:
  dd137504ecea43c97097151de5689c41b2121703

latest integrated checkpoint PR head:
  abe7194274aec8c4e277bcc5165c2156d66b53f8

latest integrated validation:
  PR Lean Fast Check run 5772 — success

current active mathematical frontier:
  physical Hamiltonian spectral theorem route
  physical spectral projection or functional-calculus layer
  positive-gap certificate from a concrete continuum scaling family
```

The active carrier now has a completed R4 Hilbert-space handoff, a completed R4 OS semigroup handoff, an OS generator input/theorem API, a Hamiltonian handoff API, a mathlib self-adjoint operator object/API/handoff, route and graph packages, direct bare-`M` boundedness endpoints, a direct boundedness public handoff, and a complete Yang-Mills direct bounded certificate surface.

The preferred current boundedness surface is the direct bare-`M` bundle.

Route-backed boundedness remains compatibility-only.

The latest certificate layer bundles the existing finite-volume/continuum construction certificate with the direct bounded R4 operator public handoff.

It does **not** add a new spectral theorem, spectral projection construction, numerical mass-gap proof, or unconditional Clay Millennium theorem.

Notation:

- `[x]` integrated and replayed on the active proof carrier;
- `[d]` open Draft PR, not integrated;
- `[r]` requires repair or reconciliation;
- `[ ]` not yet constructed or not yet physically instantiated.

A carrier theorem is not a public final theorem.

A draft PR is not an integrated layer.

A conditional theorem package or certificate surface is not a proof that the physical Yang-Mills approximation family supplies every required hypothesis.

---

## Milestone 1 — preserve finite Wilson and conditional OS foundations

Status: **available as prior theorem infrastructure**

- [x] finite Wilson Gibbs probability and conditional-law infrastructure;
- [x] finite heat-bath Hilbert and Hamiltonian theorem generators;
- [x] Dobrushin, Rayleigh, Poincare, and finite spectral-gap consequences from strict finite certificates;
- [x] conditional weak-limit, OS reconstruction, Hamiltonian, resolvent, operator-graph, and spectral-interface theorem packages;
- [x] exact internal scalar normalization and audit lanes, including the `33/20` lane;
- [x] keep these layers explicitly separated from a final physical mass-gap claim.

Definition of done:

The repository continues to distinguish finite theorem generators, conditional continuum reconstruction packages, internal normalization lanes, and physical theorem claims.

---

## Milestone 2 — maintain active proof carrier discipline

Status: **active workflow requirement**

- [x] use `formal/real-hilbert-uniform-coercive-strong-limit` as the current proof carrier;
- [x] create one focused branch for each theorem layer;
- [x] open each layer as a Draft PR;
- [x] require PR Lean Fast Check before treating the layer as integrated;
- [x] merge only after fixed-head review;
- [x] start each next layer from the updated carrier head;
- [x] do not promote draft, stale, closed-unmerged, or failing PR results into README, roadmap, or theorem-boundary language.

Definition of done:

The branch history remains a sequence of small replayable proof layers, and documentation distinguishes merged carrier facts from open or stale draft work.

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
- [x] R4 correlation structure construction;
- [x] construction-spine certificate surface.

Definition of done:

The R4 continuum-measure construction chain carries the data needed to enter reflection-positive reconstruction and certificate layers without claiming that all physical analytic estimates have been discharged.

---

## Milestone 4 — R4 reflection-positive reconstruction input

Status: **integrated on the active carrier**

- [x] reflection-positive reconstruction input closure;
- [x] propagation of reflection positivity from the measure package;
- [x] propagation of Euclidean invariance from the orbit model;
- [x] propagation of gauge invariance from the orbit model;
- [x] keep the input layer separate from the completed Hilbert-space structure.

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

## Milestone 6 — completion, completed Hilbert space, and handoff API

Status: **integrated through PR #600**

- [x] R4 completion input data;
- [x] R4 completion object data;
- [x] R4 completion map API;
- [x] R4 completion readiness API;
- [x] R4 completion transport API;
- [x] R4 final completion API;
- [x] pre-completion structure data;
- [x] quotient-to-pre-Hilbert map;
- [x] quotient-to-pre-Hilbert injectivity;
- [x] quotient inner-product well-definedness fields;
- [x] reflection-positive form descent fields;
- [x] quotient positive-definiteness fields;
- [x] completed Hilbert structure data;
- [x] standard completion carrier as `UniformSpace.Completion` of the R4 pre-Hilbert carrier;
- [x] expose the completed carrier as `r4HilbertCompletedHilbertSpace`;
- [x] expose the completed Hilbert-space handoff API for downstream OS and operator layers.

Validation receipts:

```text
PR #599 — completed Hilbert space API
PR #600 — completed Hilbert-space handoff API
```

Definition of done:

Downstream OS, semigroup, Hamiltonian, and operator layers can import one handoff API for the completed Hilbert space without restating the entire reconstruction bundle.

---

## Milestone 7 — completed OS semigroup, generator, and Hamiltonian route

Status: **integrated through PR #615**

- [x] completed R4 OS semigroup carrier;
- [x] OS time carrier, zero time, and time addition;
- [x] semigroup action, identity law, semigroup law, contraction, and strong continuity;
- [x] completed R4 OS semigroup handoff API;
- [x] infinitesimal-generator input data;
- [x] generator graph data and domain;
- [x] generator domain-to-Hilbert map and generator action;
- [x] dense-domain and closed-graph obligations;
- [x] semigroup compatibility and dissipative estimate;
- [x] generator theorem API;
- [x] Hamiltonian domain, action, and compatibility with the generator;
- [x] nonnegative-form, symmetry-on-domain, and closability input;
- [x] Hamiltonian handoff API.

Validation receipts:

```text
PR #606 — completed OS semigroup handoff
PR #608 — OS generator input API
PR #610 — OS generator theorem API
PR #615 — Hamiltonian handoff API
```

Definition of done:

The completed Hilbert space carries replayed OS semigroup, generator, and Hamiltonian handoff surfaces with explicit hypotheses and no spectral-gap claim.

---

## Milestone 8 — mathlib self-adjoint operator object and API

Status: **integrated by PR #623, PR #624, and PR #625**

- [x] construct a mathlib `LinearPMap` operator object on the completed R4 Hilbert carrier;
- [x] store the actual mathlib `IsSelfAdjoint M.mathlibOperator` predicate;
- [x] bundle compatibility with the Hamiltonian input;
- [x] bundle the existing criterion-level self-adjointness conclusion;
- [x] expose theorem-facing API projections;
- [x] expose a handoff API for later spectral-theorem layers;
- [x] keep this as an operator-object/API layer rather than a spectral theorem invocation.

Definition of done:

The R4 Hamiltonian route has a mathlib self-adjoint operator object and handoff API, without spectral projections, functional calculus, or a positive gap statement.

---

## Milestone 9 — graph, adjoint-equality, and actual-operator packages

Status: **integrated**

- [x] add project-local wrappers around pinned mathlib `LinearPMap` graph identities;
- [x] expose dense domain, closedness, and graph self-adjointness;
- [x] add operator equality packages;
- [x] add graph packages;
- [x] add actual self-adjoint package;
- [x] add actual toolkit package;
- [x] add top-witness and continuous-witness packages;
- [x] add continuous representative actual package;
- [x] add inner-action package.

Definition of done:

The operator route exposes actual operator, graph, equality, top-domain, continuous-representative, and inner-action data as stable package surfaces.

---

## Milestone 10 — bounded actual route and direct bare-M endpoint family

Status: **integrated through PR #717**

- [x] add bounded actual operator data;
- [x] add bounded route surface;
- [x] add full-domain data;
- [x] add bounded construction route data and package;
- [x] add bounded route family;
- [x] add unconditional bounded route package;
- [x] add actual route package;
- [x] add continuous representative package;
- [x] add spectral representative route;
- [x] add Hamiltonian full-domain and coverage-domain routes;
- [x] add generator-lift and generator-carrier routes;
- [x] add completed-OS, completed-Hilbert, completed-pre, and quotient-carrier routes;
- [x] add bare-`M` bounded actual route;
- [x] add central bare bounded actual route supply;
- [x] add enriched bounded actual operator data;
- [x] add enriched full-domain continuous operator data;
- [x] strengthen bare `R4HilbertMathlibSelfAdjointOperatorData` so direct bounded/full-domain evidence is carried by `M`;
- [x] add direct bare-`M` bounded-domain package;
- [x] add direct bare-`M` bounded bundle;
- [x] expose stable direct endpoint names;
- [x] expose root smoke for the direct boundedness API;
- [x] add route-backed boundedness compatibility and migration index;
- [x] add direct boundedness public handoff.

Preferred public endpoints:

```lean
r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data
r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data
r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package
```

Validation receipt:

```text
PR #717 final head:
  bf6bc9841a9f25c7276ac47bc3b9b158f87e9dcd

PR #717 merge commit on the active carrier:
  3d33df3b5c4adae03d0347403022d231d89be219

PR Lean Fast Check:
  run 5770 — success
```

Definition of done:

Bounded actual R4 operator data is available through the direct bare-`M` public endpoint family, while route-backed names remain compatibility-only.

---

## Milestone 11 — complete Yang-Mills direct bounded certificate

Status: **integrated by PR #718**

- [x] bundle the existing finite-volume and continuum construction certificate with the direct bounded R4 operator public handoff;
- [x] expose the construction-spine full spectral package through the new certificate surface;
- [x] record direct bare-`M` boundedness as primary;
- [x] keep route-backed names compatibility-only;
- [x] avoid adding a new spectral theorem;
- [x] avoid adding spectral projections;
- [x] avoid adding a numerical mass-gap claim.

Primary certificate surface:

```lean
EuclideanYangMillsCompleteConstructionDirectBoundedCertificate
```

Constructor and theorem endpoints:

```lean
euclideanYangMillsCompleteConstructionDirectBoundedCertificate

euclidean_yang_mills_complete_construction_direct_bounded_full_spectral_package

euclidean_yang_mills_complete_construction_direct_bounded_public_handoff

euclidean_yang_mills_complete_construction_direct_bounded_package
```

Validation receipt:

```text
PR #718 final head:
  abe7194274aec8c4e277bcc5165c2156d66b53f8

PR #718 merge commit on the active carrier:
  dd137504ecea43c97097151de5689c41b2121703

PR Lean Fast Check:
  run 5772 — success
```

Definition of done:

A replayed certificate surface exists for the current direct bounded construction route, while spectral theorem construction, spectral projections, physical positive-gap derivation, and final theorem language remain separate.

---

## Milestone 12 — spectral theorem layer for the physical Hamiltonian

Status: **open**

- [ ] choose or build the appropriate mathlib route for the relevant R4 Hamiltonian/operator surface;
- [ ] invoke or construct the spectral theorem interface where mathematically justified;
- [ ] expose spectral measure or projection-valued interfaces only after the route is actually constructed;
- [ ] connect the spectral interface to the current direct bounded operator route;
- [ ] keep spectral theorem use separate from a positive lower-bound claim;
- [ ] document every remaining hypothesis.

Definition of done:

The physical Hamiltonian route has a replayed spectral theorem surface without conflating it with a gap proof.

---

## Milestone 13 — physical positive-gap certificate

Status: **decisive open mathematical frontier**

- [ ] specify one concrete continuum scaling family;
- [ ] define its gauge group, lattice family, boundary conditions, observable sector, and interpolation maps;
- [ ] prove tightness or compactness estimates for that family;
- [ ] prove nontriviality of the resulting continuum limit;
- [ ] prove a uniform positive gap, mass slope, Poincare/log-Sobolev estimate, transfer contraction, or equivalent physical certificate;
- [ ] show that the certificate feeds the completed Hamiltonian spectral-gap interface.

Definition of done:

A positive mass-gap lower bound is derived from the actual physical approximation family rather than supplied as an abstract input.

---

## Milestone 14 — final theorem and external review

Status: **not claimed**

- [ ] assemble a single replayable final theorem path;
- [ ] remove or discharge all nonphysical placeholders;
- [ ] document every remaining hypothesis and every theorem dependency;
- [ ] pass internal review gates;
- [ ] obtain independent external mathematical review;
- [ ] only then consider public final theorem language.

Definition of done:

The repository can state a final theorem without conflating finite-volume results, conditional transfer theorems, internal normalization lanes, completed Hilbert-space and OS layers, self-adjoint operator API work, boundedness handoff surfaces, construction-certificate surfaces, and the actual four-dimensional Yang-Mills mass-gap theorem.
