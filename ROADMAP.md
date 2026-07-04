# MGAP4D Roadmap

This roadmap records the active proof-development path of `itakura-hidetoshi/4d-mass-gap`.

## Snapshot — 2026-07-05

```text
active proof carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

latest integrated carrier PR:
  PR #539 — Add R4 Hilbert reconstruction quotient section range uniqueness layer

latest integrated carrier merge commit:
  1364ddc7f57a98a49482d81ec474e152d962ccee

latest integrated carrier PR head:
  0de760e4b70749942aac5e61efb189143e6e315a

latest integrated validation:
  PR Lean Fast Check run 5554 — success

current open draft frontier:
  PR #540 — Add R4 Hilbert reconstruction quotient map injectivity layer
  head da05bf98e9c3f87f3d363e189c6a91d45d5ec7ae
  PR Lean Fast Check run 5555 — failure
```

The repository does **not** yet prove an unconditional interacting four-dimensional continuum Yang--Mills theory, a completed physical Hilbert reconstruction, a self-adjoint physical Hamiltonian, or a physical mass gap from one fully instantiated continuum scaling trajectory.

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
- [ ] keep these layers explicitly separated from a final physical mass-gap claim.

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
- [ ] do not promote draft or failing PR results into README, roadmap, or theorem-boundary language.

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
- [ ] keep the input layer separate from the completed Hilbert-space structure.

Definition of done:

The reconstruction input surface is available as a formal source of reflection-positive, Euclidean-invariant, and gauge-invariant data for later quotient and Hilbert reconstruction layers.

---

## Milestone 5 — R4 Hilbert reconstruction carrier

Status: **integrated on the active carrier**

- [x] define the reconstruction input carrier;
- [x] package the Hilbert reconstruction carrier closure;
- [x] expose the carrier as the domain for quotient construction;
- [ ] avoid presenting the carrier as a completed Hilbert space.

Definition of done:

The carrier exists as the pre-Hilbert or input side of the reconstruction route, with later quotient, norm, inner-product, and completion layers still visible.

---

## Milestone 6 — R4 equality quotient and projection stack

Status: **integrated on the active carrier through PR #539**

- [x] equality quotient carrier;
- [x] canonical quotient map;
- [x] quotient projection layer;
- [x] representative-choice layer;
- [x] quotient section layer;
- [x] proof that projecting the section returns the original quotient class;
- [x] quotient-section injectivity layer;
- [x] quotient-section range layer;
- [x] quotient-section range uniqueness layer.

The latest integrated layer, PR #539, packages:

```text
witness uniqueness
projection uniqueness
full witness uniqueness
Function.Injective quotientSection
reflection positivity
Euclidean invariance
gauge invariance
```

Validation receipt:

```text
PR #539 final head:
  0de760e4b70749942aac5e61efb189143e6e315a

PR #539 merge commit on the active carrier:
  1364ddc7f57a98a49482d81ec474e152d962ccee

PR Lean Fast Check:
  run 5554 — success
```

Definition of done:

The quotient section and its range have uniqueness properties strong enough to support downstream well-definedness proofs for quotient-level analytic structure.

---

## Milestone 7 — quotient-map injectivity frontier

Status: **Draft PR #540; not integrated**

- [d] prove that the current equality quotient map reflects input-carrier equality;
- [d] prove `Function.Injective quotientMap` for the reconstruction quotient carrier;
- [d] package model, theorem, closure, and compile-check coverage;
- [r] repair the current PR Lean Fast Check failure before integration;
- [ ] after a successful fixed-head replay, merge into the active carrier.

Current receipt:

```text
PR #540 head:
  da05bf98e9c3f87f3d363e189c6a91d45d5ec7ae

PR Lean Fast Check:
  run 5555 — failure
```

Definition of done:

The quotient-map injectivity theorem is replay-clean, merged into the active carrier, and documented as integrated only after the failed draft state is repaired.

---

## Milestone 8 — quotient norm and inner-product well-definedness

Status: **open**

- [ ] define the quotient-level norm or seminorm;
- [ ] prove representative independence for the norm;
- [ ] define the quotient-level bilinear form or inner product;
- [ ] prove representative independence for the inner product;
- [ ] prove positivity and null-space consistency;
- [ ] connect reflection positivity to the quotient positivity statement;
- [ ] preserve Euclidean and gauge invariance through the quotient analytic structure.

Definition of done:

The quotient carrier supports well-defined analytic data that no longer depend on the selected representative.

---

## Milestone 9 — algebraic and normed-space structure on the quotient

Status: **open**

- [ ] define addition on quotient classes;
- [ ] define scalar multiplication on quotient classes;
- [ ] prove well-definedness of addition;
- [ ] prove well-definedness of scalar multiplication;
- [ ] construct additive and scalar algebraic instances;
- [ ] prove norm compatibility with the algebraic operations;
- [ ] construct the normed-space or seminormed-space layer;
- [ ] construct the inner-product-space layer once positivity is sufficient.

Definition of done:

The quotient is no longer only a setoid/representative object; it has the algebraic and analytic structure needed for completion.

---

## Milestone 10 — complete the Hilbert space

Status: **open**

- [ ] construct Cauchy sequences or completion data;
- [ ] build the completed carrier;
- [ ] prove the completion map is isometric or norm-compatible;
- [ ] prove density of the image of the quotient carrier;
- [ ] establish `CompleteSpace` for the completed carrier;
- [ ] establish the Hilbert-space instance;
- [ ] define the physical state map into the completed space;
- [ ] prove density of the physical observable states when required.

Definition of done:

The reconstruction route has a completed real Hilbert space, not merely a quotient carrier with representative bookkeeping.

---

## Milestone 11 — OS semigroup and physical Hamiltonian on the completed space

Status: **open**

- [ ] define the OS contraction semigroup on the completed Hilbert space;
- [ ] prove strong continuity;
- [ ] identify the generator;
- [ ] define the physical Hamiltonian;
- [ ] prove nonnegativity;
- [ ] prove symmetry or self-adjointness under explicit hypotheses;
- [ ] connect the Hamiltonian to the prior conditional OS/operator-limit packages;
- [ ] expose the exact assumptions needed for a spectral-gap theorem.

Definition of done:

The completed Hilbert space carries a closed self-adjoint physical Hamiltonian with visible hypotheses and replayed Lean interfaces.

---

## Milestone 12 — physical positive-gap certificate

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

## Milestone 13 — final theorem and external review

Status: **not claimed**

- [ ] assemble a single replayable final theorem path;
- [ ] remove or discharge all nonphysical placeholders;
- [ ] document every remaining hypothesis and every theorem dependency;
- [ ] pass internal review gates;
- [ ] obtain independent external mathematical review;
- [ ] only then consider public final theorem language.

Definition of done:

The repository can state a final theorem without conflating finite-volume results, conditional transfer theorems, internal normalization lanes, and the actual four-dimensional Yang--Mills mass-gap theorem.
