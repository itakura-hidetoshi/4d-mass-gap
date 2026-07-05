# MGAP4D Roadmap

This roadmap records the active proof-development path of `itakura-hidetoshi/4d-mass-gap`.

## Snapshot — 2026-07-05

```text
active proof carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

latest integrated carrier PR:
  PR #599 — Add R4 completed Hilbert space API

latest integrated carrier merge commit:
  a4beaab42037db3f974574c44bfbb114b1c5d934

latest integrated carrier PR head:
  4c9e3b83f46b59e7a9dac9802824ac707f95a8fa

latest integrated validation:
  PR Lean Fast Check run 5625 — success

current open draft frontier:
  PR #600 — Add R4 completed Hilbert space handoff API
  head b6a3b450bddfca55549653975f5cfa742f7e97f6
```

The repository now has an integrated completed R4 Hilbert-space API object on the active carrier.

It still does **not** prove an unconditional interacting four-dimensional continuum Yang--Mills theory, a self-adjoint physical Hamiltonian, or a physical mass gap from one fully instantiated continuum scaling trajectory.

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

## Milestone 7 — pre-Hilbert and completed-structure data

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
- [x] completed actual API projections.

Definition of done:

The reconstruction route has moved from quotient bookkeeping to actual pre-Hilbert and completed-structure data, while preserving which statements are data fields and which are theorem consequences.

---

## Milestone 8 — standard completion identity and quotient route

Status: **integrated on the active carrier**

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

## Milestone 9 — quotient-dense standard completion data and theorem API

Status: **integrated on the active carrier**

- [x] data layer carrying actual `DenseRange` for the quotient-to-standard-completion map;
- [x] theorem API exposing dense range for the original quotient map itself;
- [x] theorem API exposing pre-density, quotient-density, factorization, and route readiness;
- [x] construction bundle for the standard real Hilbert completion.

Definition of done:

The quotient-to-completion map itself is available as a dense map into the standard completed carrier.

---

## Milestone 10 — completed R4 Hilbert space API

Status: **integrated by PR #599**

- [x] expose the completed carrier as `r4HilbertCompletedHilbertSpace`;
- [x] project `NormedAddCommGroup` for the completed space;
- [x] project real `InnerProductSpace ℝ` for the completed space;
- [x] project `CompleteSpace` for the completed space;
- [x] expose the dense pre-Hilbert map;
- [x] expose the dense quotient map;
- [x] prove equality with `UniformSpace.Completion` of the R4 pre-Hilbert carrier;
- [x] expose quotient-map factorization through the pre-Hilbert carrier;
- [x] bundle the completed Hilbert-space construction theorem.

Validation receipt:

```text
PR #599 final head:
  4c9e3b83f46b59e7a9dac9802824ac707f95a8fa

PR #599 merge commit on the active carrier:
  a4beaab42037db3f974574c44bfbb114b1c5d934

PR Lean Fast Check:
  run 5625 — success
```

Definition of done:

The active carrier has a completed real Hilbert-space object for the formal R4 reconstruction route.

---

## Milestone 11 — completed Hilbert-space handoff API

Status: **Draft PR #600; not integrated in this roadmap**

- [d] expose a handoff carrier for downstream layers;
- [d] expose handoff pre-Hilbert and quotient maps;
- [d] bundle dense pre-Hilbert and quotient maps;
- [d] bundle quotient factorization;
- [d] bundle route readiness;
- [d] keep the handoff layer separate from Hamiltonian and spectral-gap claims;
- [ ] merge only after PR Lean Fast Check succeeds and fixed-head review is complete.

Current receipt:

```text
PR #600 head:
  b6a3b450bddfca55549653975f5cfa742f7e97f6

PR Lean Fast Check:
  run 5626 — in progress at the time of this update
```

Definition of done:

Downstream OS, semigroup, and Hamiltonian layers can import one handoff API for the completed Hilbert space without restating the entire reconstruction bundle.

---

## Milestone 12 — OS semigroup on the completed Hilbert space

Status: **open**

- [ ] define the OS contraction semigroup on the completed Hilbert space;
- [ ] prove strong continuity;
- [ ] identify the generator candidate;
- [ ] connect the completed Hilbert-space object to the prior conditional OS/operator-limit packages;
- [ ] expose all assumptions needed by the semigroup layer.

Definition of done:

The completed Hilbert space carries a replayed OS semigroup interface with explicit hypotheses.

---

## Milestone 13 — physical Hamiltonian on the completed Hilbert space

Status: **open**

- [ ] define the physical Hamiltonian as the generator of the OS semigroup;
- [ ] prove nonnegativity;
- [ ] prove closedness;
- [ ] prove symmetry or self-adjointness under explicit hypotheses;
- [ ] expose spectral theorem interfaces;
- [ ] separate Hamiltonian construction from any positive-gap claim.

Definition of done:

The completed Hilbert space carries a closed self-adjoint physical Hamiltonian with visible hypotheses and replayed Lean interfaces.

---

## Milestone 14 — physical positive-gap certificate

Status: **decisive open mathematical frontier**

- [ ] specify one concrete continuum scaling family;
- [ ] define its gauge group, lattice family, boundary conditions, observable sector, and interpolation maps;
- [ ] prove tightness or compactness estimates for that family;
- [ ] prove nontriviality of the resulting continuum limit;
- [ ] prove a uniform positive gap, mass slope, Poincare/log-Sobolev estimate, transfer contraction, or equivalent physical certificate;
- [ ] show that the certificate feeds the completed Hamiltonian gap interface.

Definition of done:

A positive mass-gap lower bound is derived from the actual physical approximation family rather than supplied as an abstract input.

---

## Milestone 15 — final theorem and external review

Status: **not claimed**

- [ ] assemble a single replayable final theorem path;
- [ ] remove or discharge all nonphysical placeholders;
- [ ] document every remaining hypothesis and every theorem dependency;
- [ ] pass internal review gates;
- [ ] obtain independent external mathematical review;
- [ ] only then consider public final theorem language.

Definition of done:

The repository can state a final theorem without conflating finite-volume results, conditional transfer theorems, internal normalization lanes, completed Hilbert-space API work, and the actual four-dimensional Yang--Mills mass-gap theorem.
