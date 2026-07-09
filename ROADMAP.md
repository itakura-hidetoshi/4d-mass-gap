# MGAP4D Roadmap

This roadmap records the active proof-development path of `itakura-hidetoshi/4d-mass-gap`.

## Snapshot — 2026-07-09

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

The active carrier now has a completed R4 Hilbert-space handoff, a completed R4 OS semigroup handoff, an OS generator input/theorem API, a Hamiltonian handoff API, a mathlib self-adjoint operator object/API/handoff, and a direct bounded actual operator public handoff.

The preferred current boundedness surface is the direct bare-`M` bundle.

Route-backed boundedness remains available as compatibility-only.

The repository still does **not** prove an unconditional interacting four-dimensional continuum Yang--Mills theory, a physical positive spectral gap from one fully instantiated continuum scaling trajectory, or a Clay Millennium mass-gap theorem.

Notation:

- `[x]` integrated and replayed on the active proof carrier;
- `[d]` open Draft PR, not integrated;
- `[r]` requires repair or reconciliation;
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
- [x] do not promote draft or failing PR results into README, roadmap, or theorem-boundary language.

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

## Milestone 6 — completion input, object, and readiness APIs

Status: **integrated on the active carrier**

- [x] R4 completion input data;
- [x] R4 completion object data;
- [x] R4 completion map API;
- [x] R4 completion readiness API;
- [x] R4 completion transport API;
- [x] R4 final completion API.

Definition of done:

The completion route exposes its input, object, map, readiness, and transport obligations without asserting the completed Hilbert space before the required analytic data are available.

---

## Milestone 7 — pre-Hilbert, completed structure, and standard completion

Status: **integrated on the active carrier**

- [x] pre-completion structure data;
- [x] quotient-to-pre-Hilbert map;
- [x] quotient-to-pre-Hilbert injectivity;
- [x] quotient inner-product well-definedness fields;
- [x] reflection-positive form descent fields;
- [x] quotient positive-definiteness fields;
- [x] completed Hilbert structure data;
- [x] complete-space field for the completed carrier;
- [x] dense-range data for the pre-to-completed and quotient-to-completed maps;
- [x] standard completion carrier as `UniformSpace.Completion` of the R4 pre-Hilbert carrier;
- [x] standard completion map from the pre-Hilbert carrier;
- [x] real inner-product projection for the standard completion;
- [x] `CompleteSpace` projection for the standard completion;
- [x] dense range of the standard completion map;
- [x] quotient-to-standard-completion route;
- [x] quotient map factorization through the pre-Hilbert carrier.

Definition of done:

The carrier is definitionally tied to the mathlib completion route rather than only to an abstract completed carrier.

---

## Milestone 8 — completed R4 Hilbert space and handoff API

Status: **integrated**

- [x] expose the completed carrier as `r4HilbertCompletedHilbertSpace`;
- [x] project `NormedAddCommGroup` for the completed space;
- [x] project real `InnerProductSpace ℝ` for the completed space;
- [x] project `CompleteSpace` for the completed space;
- [x] expose the dense pre-Hilbert map;
- [x] expose the dense quotient map;
- [x] prove equality with `UniformSpace.Completion` of the R4 pre-Hilbert carrier;
- [x] expose quotient-map factorization through the pre-Hilbert carrier;
- [x] bundle the completed Hilbert-space construction theorem;
- [x] expose the completed Hilbert-space handoff API for downstream OS/operator layers.

Validation receipts:

```text
PR #599:
  completed Hilbert space API

PR #600:
  completed Hilbert-space handoff API
```

Definition of done:

Downstream OS, semigroup, and Hamiltonian layers can import one handoff API for the completed Hilbert space without restating the entire reconstruction bundle.

---

## Milestone 9 — completed OS semigroup handoff

Status: **integrated by PR #606**

- [x] expose the completed R4 OS semigroup carrier;
- [x] expose the time carrier, zero time, and time addition;
- [x] expose the semigroup action;
- [x] package identity law and semigroup law;
- [x] package contraction;
- [x] package strong continuity;
- [x] package compatibility and readiness;
- [x] keep the layer before generator, Hamiltonian, spectral theorem, and spectral-gap claims.

Definition of done:

The completed Hilbert space carries a replayed OS semigroup handoff interface with explicit hypotheses and no gap claim.

---

## Milestone 10 — OS generator input and theorem API

Status: **integrated by PR #608 and PR #610**

- [x] add infinitesimal-generator input data for the completed R4 OS semigroup;
- [x] keep the generator as explicit graph data with separate domain;
- [x] expose the domain-to-Hilbert map and generator action;
- [x] package dense-domain and closed-graph obligations;
- [x] package semigroup compatibility and dissipative estimate;
- [x] re-expose the input surface as a theorem API;
- [x] avoid identifying the generator with a physical Hamiltonian at this layer.

Definition of done:

The OS generator has a theorem-facing API with explicit graph and domain obligations, without self-adjointness or spectral-gap claims.

---

## Milestone 11 — Hamiltonian handoff API

Status: **integrated by PR #615**

- [x] expose generator data;
- [x] expose the completed carrier;
- [x] expose Hamiltonian domain;
- [x] expose domain-to-generator map;
- [x] expose Hamiltonian action;
- [x] package upstream generator handoff;
- [x] package compatibility with the generator;
- [x] package nonnegative-form input;
- [x] package symmetry-on-domain input;
- [x] package closability input;
- [x] expose readiness and bundled handoff theorem;
- [x] keep the layer separate from self-adjointness, spectral theorem, and gap claims.

Definition of done:

The Hamiltonian route has a replayable handoff surface, but still requires later self-adjoint, spectral, and gap layers.

---

## Milestone 12 — mathlib self-adjoint operator object and API

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

## Milestone 13 — graph, adjoint-equality, and actual-operator packages

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

The operator route can expose actual operator, graph, equality, top-domain, continuous-representative, and inner-action data as stable package surfaces.

---

## Milestone 14 — bounded actual route and direct bare-M endpoint family

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

## Milestone 15 — complete Yang-Mills direct bounded certificate

Status: **open draft frontier in PR #718**

- [d] bundle the existing finite-volume and continuum construction certificate with the direct bounded R4 operator public handoff;
- [d] expose the construction-spine full spectral package through the new certificate surface;
- [d] record direct bare-`M` boundedness as primary;
- [d] keep route-backed names compatibility-only;
- [d] avoid adding a new spectral theorem;
- [d] avoid adding spectral projections;
- [d] avoid adding a numerical mass-gap claim.

Definition of done:

A replayed certificate surface exists for the current direct bounded construction route, with no promotion to physical mass-gap language.

---

## Milestone 16 — spectral theorem layer for the physical Hamiltonian

Status: **open**

- [ ] invoke or construct the appropriate spectral theorem interface for the mathlib self-adjoint Hamiltonian object;
- [ ] expose spectral measure or projection-valued interfaces where mathematically justified;
- [ ] keep spectral theorem use separate from a positive lower-bound claim;
- [ ] connect the spectral interface to the current direct bounded operator route;
- [ ] document every remaining hypothesis.

Definition of done:

The physical Hamiltonian route has a replayed spectral theorem surface without conflating it with a gap proof.

---

## Milestone 17 — physical positive-gap certificate

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

## Milestone 18 — final theorem and external review

Status: **not claimed**

- [ ] assemble a single replayable final theorem path;
- [ ] remove or discharge all nonphysical placeholders;
- [ ] document every remaining hypothesis and every theorem dependency;
- [ ] pass internal review gates;
- [ ] obtain independent external mathematical review;
- [ ] only then consider public final theorem language.

Definition of done:

The repository can state a final theorem without conflating finite-volume results, conditional transfer theorems, internal normalization lanes, completed Hilbert-space and OS layers, self-adjoint operator API work, boundedness handoff surfaces, and the actual four-dimensional Yang--Mills mass-gap theorem.
