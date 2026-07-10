# MGAP4D Roadmap

This roadmap records the authoritative proof-development path of `itakura-hidetoshi/4d-mass-gap`.

## Snapshot — 2026-07-10 JST

```text
active proof carrier:
  formal/real-hilbert-uniform-coercive-strong-limit

latest integrated theorem checkpoint:
  PR #746 — Identify direct bounded exact first excitation

latest integrated PR head:
  a38aea205dce9fe07b949c2e1b34cb3a160ac927

latest integrated merge commit:
  f300370b08736240342cb05885e6ffa7a174ed1b

latest validation:
  PR Lean Fast Check run 5807 — success

post-merge comparison:
  f300370b08736240342cb05885e6ffa7a174ed1b
  versus formal/real-hilbert-uniform-coercive-strong-limit
  identical
```

The active carrier now contains an exact lower-spectrum theorem chain for every supplied:

```lean
S : EuclideanYangMillsContinuumMeasureConstructionSpine
```

The current integrated endpoint identifies:

```text
exactGapValueReal
  = the attained least nonzero spectral energy
  = the infimum of the nonzero spectrum
  = the reconstructed model first excitation.
```

It also proves the exact vacuum-to-first-excitation spectral separation and transports the existing first-excitation PVM witness to the singleton at `exactGapValueReal`.

The decisive open frontier is to construct and validate the required construction spine from one concrete physical four-dimensional Yang--Mills approximation family.

## Status notation

- `[x]` means integrated and replayed on the active proof carrier.
- `[d]` means an open Draft PR that is not integrated.
- `[r]` means a layer requires repair, reconciliation, or replacement.
- `[ ]` means the layer has not been constructed or has not been physically instantiated.

A merged carrier theorem is not automatically a public final theorem.

A theorem parametrized by a construction spine does not prove that a concrete physical family supplies that spine.

A spectral or PVM field carried by an input structure is not the same as deriving that field from a physical continuum construction.

## Current priority

The next substantial work should reduce the distance between the exact-gap theorem chain and a concrete physical approximation family.

Priority order:

```text
1. identify every field of EuclideanYangMillsContinuumMeasureConstructionSpine used by the #744–#746 theorem chain;
2. classify each field as constructed, transported, conditional, normalized, or still supplied;
3. choose one concrete gauge-theory approximation family;
4. prove the spine fields from that family in dependency order;
5. reconnect the resulting physical construction to the exact-gap certificate;
6. perform independent mathematical review before any final theorem claim.
```

Additional wrapper, alias, smoke, or receipt layers count as progress only when they stabilize a necessary public API, remove duplicated destructuring, expose an actual theorem dependency, or connect the theorem chain to the physical construction frontier.

---

## Milestone 1 — preserve finite-volume and conditional foundations

Status: **available as prior theorem infrastructure**

- [x] finite Wilson Gibbs probability and conditional-law infrastructure;
- [x] finite heat-bath Hilbert and Hamiltonian theorem generators;
- [x] Dobrushin, Rayleigh, Poincare, and finite spectral-gap consequences from strict finite certificates;
- [x] conditional weak-limit, OS reconstruction, Hamiltonian, resolvent, operator-graph, and spectral-interface theorem packages;
- [x] exact internal normalization and provenance lanes, including the `33/20` route;
- [x] keep finite-volume, conditional continuum, normalization, and physical theorem claims distinct.

Definition of done:

The repository retains reusable finite and conditional theorem generators without presenting them as an unconditional four-dimensional continuum Yang--Mills theorem.

---

## Milestone 2 — maintain active proof-carrier discipline

Status: **active workflow requirement**

- [x] use `formal/real-hilbert-uniform-coercive-strong-limit` as the authoritative proof carrier;
- [x] create one focused branch for each theorem or documentation layer;
- [x] open each layer as a Draft PR;
- [x] require PR Lean Fast Check before integration;
- [x] review and merge a fixed head SHA;
- [x] verify that the merge commit is identical to the updated carrier head;
- [x] start the next layer from the updated carrier;
- [x] exclude stale, superseded, closed-unmerged, and failing PRs from current-status claims.

Definition of done:

The carrier history remains a replayable sequence of focused layers with explicit validation receipts.

---

## Milestone 3 — R4 reconstruction through completed Hilbert space

Status: **integrated**

- [x] R4 continuum-measure construction-spine surface;
- [x] gauge-field and gauge-action construction layers;
- [x] gauge-invariant and Schwinger construction layers;
- [x] n-point family, correlation functional, and correlation structure;
- [x] reflection-positive reconstruction input;
- [x] quotient carrier, projection, representative, section, range, and transport APIs;
- [x] pre-Hilbert structure and standard real Hilbert completion;
- [x] completed Hilbert carrier exposed as `r4HilbertCompletedHilbertSpace`;
- [x] completed Hilbert-space handoff API.

Definition of done:

The formal reconstruction route reaches a standard completed real Hilbert carrier and exposes a stable handoff to OS and operator layers.

---

## Milestone 4 — OS semigroup, generator, Hamiltonian, and self-adjoint operator

Status: **integrated**

- [x] completed R4 OS semigroup and handoff;
- [x] generator input and theorem APIs;
- [x] Hamiltonian domain, action, compatibility, and handoff;
- [x] mathlib `LinearPMap` operator object;
- [x] `IsSelfAdjoint M.mathlibOperator` surface;
- [x] graph, dense-domain, closedness, formal-adjoint, and adjoint-equality packages;
- [x] actual-operator, equality, graph, and inner-action packages;
- [x] continuous self-adjoint representative packages.

Definition of done:

The reconstructed Hilbert route exposes a theorem-facing self-adjoint operator and its graph and adjoint infrastructure.

---

## Milestone 5 — direct bare-M bounded route

Status: **integrated through PR #717**

- [x] bounded actual operator data;
- [x] full-domain continuous representative data;
- [x] direct bare-`M` bounded-domain package;
- [x] direct bare-`M` bounded bundle;
- [x] stable direct endpoint names;
- [x] root smoke coverage;
- [x] migration index marking direct bare-`M` boundedness as primary;
- [x] route-backed boundedness retained as compatibility-only;
- [x] public boundedness handoff.

Preferred endpoints:

```lean
r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data
r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data
r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package
```

Definition of done:

Downstream theorem layers can consume bounded actual R4 operator data without carrying an external route witness.

---

## Milestone 6 — complete-construction direct bounded certificate

Status: **integrated by PR #718**

- [x] bundle the finite-volume and continuum construction certificate with the direct bounded public handoff;
- [x] expose the construction-spine full spectral package through the certificate;
- [x] preserve direct bare-`M` boundedness as the primary route;
- [x] preserve route-backed names as compatibility-only;
- [x] keep the certificate separate from an unconditional physical construction claim.

Primary surface:

```lean
EuclideanYangMillsCompleteConstructionDirectBoundedCertificate
```

Definition of done:

A single certificate surface connects the construction spine, spectral package, and direct bounded operator route.

---

## Milestone 7 — stable downstream and public-consumer API

Status: **integrated through PR #743**

- [x] root exposure of the direct bounded certificate;
- [x] complete-construction public handoff;
- [x] root public API and canonical bundle;
- [x] ordered public surface and merge-order coherence bridge;
- [x] downstream public surface and stable public API leaf;
- [x] downstream import smoke;
- [x] theorem-facing downstream package;
- [x] public consumer package;
- [x] public consumer accessors and endpoint theorems;
- [x] public consumer smoke and root API;
- [x] compact route and endpoint-name receipts.

Definition of done:

Downstream files can consume the direct bounded certificate and its principal spectral facts through stable imports without repeatedly destructuring large structures.

---

## Milestone 8 — positive nonzero-spectrum and lower-bound packages

Status: **integrated through PR #739**

- [x] connect the downstream package to the construction-spine spectral certificate;
- [x] prove positivity of every nonzero spectral energy;
- [x] prove positivity of the nonzero-spectrum infimum;
- [x] expose positive and nonnegative spectrum-subset packages;
- [x] package a positive lower-bound witness;
- [x] factor the lower-bound ray through the positive real ray;
- [x] combine positivity, nonzeroness, infimum, and lower-bound facts into certified spectrum packages.

Definition of done:

The theorem-facing API exposes reusable order-theoretic consequences of the supplied spectral-gap package.

---

## Milestone 9 — exact-gap interval certificate

Status: **integrated by PR #744**

- [x] specialize the Hamiltonian mass-gap theorem to the complete construction spine;
- [x] prove the spectrum lies in the vacuum point or the closed ray above `exactGapValueReal`;
- [x] prove the open interval between zero and `exactGapValueReal` contains no spectral point;
- [x] prove `exactGapValueReal` belongs to the energy spectrum;
- [x] prove it is the least nonzero spectral energy;
- [x] prove both orientations of the nonzero-spectrum infimum identity;
- [x] package the results with the compact root consumer API.

Primary surface:

```lean
EuclideanYangMillsCompleteConstructionDirectBoundedExactGapIntervalCertificate
```

Main compact endpoint:

```lean
euclideanYangMillsCompleteConstructionDirectBounded_exactGapIntervalCertificate_complete
```

Definition of done:

For every supplied construction spine, the exact gap is an attained least nonzero spectral value and isolates the vacuum.

---

## Milestone 10 — exact threshold spectral classification

Status: **integrated by PR #745**

- [x] prove the nonzero spectrum is disjoint from `Set.Iio exactGapValueReal`;
- [x] prove the full spectrum below the threshold is exactly `{0}`;
- [x] prove the nonzero spectrum at or below the threshold is exactly `{exactGapValueReal}`;
- [x] prove the full spectrum at or below the threshold is exactly `{0, exactGapValueReal}`;
- [x] package the classification with the exact-gap interval certificate.

Primary surface:

```lean
EuclideanYangMillsCompleteConstructionDirectBoundedExactThresholdSeparationCertificate
```

Main compact endpoint:

```lean
euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparation_complete
```

Definition of done:

The lower spectrum is classified exactly at the vacuum and first nonzero threshold for every supplied construction spine.

---

## Milestone 11 — exact first-excitation identification

Status: **integrated by PR #746**

- [x] prove the model first excitation equals `exactGapValueReal`;
- [x] prove the first excitation belongs to the nonzero spectrum;
- [x] prove it is the least nonzero spectral energy;
- [x] prove uniqueness of the least nonzero spectral energy;
- [x] transport the first-excitation PVM witness to `{exactGapValueReal}`;
- [x] re-express strict and closed sublevel classifications at `firstExcitation`;
- [x] package the equality, leastness, uniqueness, PVM witness, and threshold separation.

Primary surface:

```lean
EuclideanYangMillsCompleteConstructionDirectBoundedExactFirstExcitationCertificate
```

Main compact endpoint:

```lean
euclideanYangMillsCompleteConstructionDirectBounded_exactFirstExcitation_complete
```

Validation receipt:

```text
PR #746 head:
  a38aea205dce9fe07b949c2e1b34cb3a160ac927

PR #746 merge commit:
  f300370b08736240342cb05885e6ffa7a174ed1b

PR Lean Fast Check:
  run 5807 — success

post-merge carrier comparison:
  identical
```

Definition of done:

For every supplied construction spine, the first excitation is exactly the attained unique least nonzero spectral energy and has a singleton spectral-PVM witness.

---

## Milestone 12 — construction-spine dependency reduction

Status: **active mathematical frontier**

- [ ] enumerate the fields of `EuclideanYangMillsContinuumMeasureConstructionSpine` used transitively by the exact-gap interval, threshold, and first-excitation certificates;
- [ ] record the source theorem or assumption for each field;
- [ ] distinguish data proved from finite Wilson or continuum construction from data imported through a spectral certificate;
- [ ] identify every circular, normalization-only, or theorem-body-origin dependency;
- [ ] replace supplied fields with derived fields where an upstream theorem already exists;
- [ ] expose a minimal physical-input structure with no redundant certificate fields;
- [ ] prove that the exact-gap endpoint factors through that minimal structure.

Definition of done:

The exact-gap theorem chain has a transparent dependency boundary, and every remaining supplied field corresponds to a genuine unresolved physical or analytic obligation.

---

## Milestone 13 — concrete physical construction-spine instantiation

Status: **decisive open mathematical frontier**

- [ ] choose one concrete compact gauge group and approximation family;
- [ ] specify the lattice or regularization sequence, boundary conditions, interpolation maps, and observable algebra;
- [ ] prove gauge invariance and the required finite-volume consistency;
- [ ] prove tightness, compactness, or another continuum-existence mechanism;
- [ ] prove nontriviality of the continuum limit;
- [ ] prove Euclidean covariance and reflection positivity for the limit;
- [ ] construct the physical Hilbert space, vacuum, semigroup, generator, and Hamiltonian from that family;
- [ ] prove the self-adjointness and spectral/PVM data required by the construction spine;
- [ ] derive the positive exact-gap data from the physical family rather than supplying it as a spine field;
- [ ] instantiate `EuclideanYangMillsContinuumMeasureConstructionSpine` with the resulting construction.

Definition of done:

A concrete physical approximation family produces the complete construction spine used by the #744–#746 theorem chain.

---

## Milestone 14 — physical normalization and scope

Status: **open**

- [ ] verify that the Hamiltonian and mass normalization correspond to the intended four-dimensional Yang--Mills theory;
- [ ] separate dimensionless internal normalization from a physical mass scale;
- [ ] justify the role of the upstream `33/20` theorem in the physical construction;
- [ ] prove that the continuum theory is interacting and nontrivial;
- [ ] state the gauge group and theorem scope without hidden generalization;
- [ ] eliminate nonphysical placeholders and theorem-body-origin shortcuts from the final dependency path.

Definition of done:

The exact-gap value has a mathematically and physically justified interpretation in the instantiated continuum theory.

---

## Milestone 15 — final theorem and independent review

Status: **not claimed**

- [ ] assemble one replayable theorem path from the concrete approximation family to the final mass-gap statement;
- [ ] document every hypothesis and dependency;
- [ ] ensure that no essential physical conclusion is stored as an input field;
- [ ] pass repository validation and theorem-dependency checks;
- [ ] obtain independent expert review of the mathematical argument and the Lean formalization;
- [ ] reconcile the result with the precise Clay problem statement;
- [ ] only then consider unconditional final-theorem language.

Definition of done:

The repository can state a final theorem without conflating formal consequences of a supplied construction spine with the construction of the physical four-dimensional Yang--Mills theory itself.

## Non-claims at the current checkpoint

The active carrier does not yet establish:

```text
an unconditional construction of the required continuum Yang-Mills spine;
a proof that one specified physical approximation family supplies every spine field;
an independently validated interacting four-dimensional continuum theory;
a physical derivation of the exact-gap normalization from that family;
an unconditional Clay Millennium Yang-Mills mass-gap theorem;
independent external mathematical consensus.
```

The integrated #744–#746 results are substantial exact spectral consequences inside the supplied construction spine.

They should be described as such, neither weakened to mere documentation nor promoted beyond their actual dependency boundary.
