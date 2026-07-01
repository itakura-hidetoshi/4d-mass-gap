# MGAP4D Roadmap

This roadmap records the active proof-development path of `itakura-hidetoshi/4d-mass-gap`.

## Snapshot — 2026-07-01

```text
latest mathematical proof checkpoint on main:
  a80a75449a16d07889519c1823595c5244824583

latest merged mathematical proof PR on main:
  PR #300

current main documentation head:
  e20a26cc3034c2e5c793d371b034585ab57cc385

active proof carrier:
  formal/real-hilbert-uniform-coercive-strong-limit
  7f1dae659bef10ea1713d57d20a620d1065fbf1d

latest integrated proof PR on the carrier:
  PR #364

latest validation:
  PR #364 head 67428df16f4057b7956f2b873a90c639572d070d
  PR Lean Fast Check run 5205 — success

carrier relative to current main documentation head:
  ahead 359
  behind 169
  merge base 929e20583ae368475d4bedb65c060c2d3c4c0fff
```

The repository does not yet prove an unconditional interacting four-dimensional continuum Yang--Mills theory or a physical mass gap derived from a concrete continuum scaling trajectory.

Notation:

- `[x]` merged and replayed on `main`;
- `[c]` integrated and replayed on the active proof carrier, but not on `main`;
- `[p]` represented by an open PR against `main`;
- `[ ]` incomplete or not yet instantiated physically.

A carrier merge is not a `main` merge.

## Completed on `main`

### Finite compact Wilson probability and reflection theory

- [x] positive-physical-link compact gauge configuration space;
- [x] normalized product Haar probability measure;
- [x] Wilson Gibbs density and probability measure;
- [x] finite gauge invariance;
- [x] periodic translation invariance;
- [x] standard `SU(N)` Wilson energy with `0 <= E_W <= 2`;
- [x] exact four-dimensional periodic incidence and plaquette counts;
- [x] even-periodic reflection geometry;
- [x] positive, negative, and boundary coordinate sectors;
- [x] Haar factorization across the reflection boundary;
- [x] Wilson Gibbs density factorization;
- [x] local positive-semidefinite crossing kernels;
- [x] bounded-continuous finite Gibbs reflection positivity.

### Orientation-correct Dobrushin and finite Hamiltonian theory

- [x] exact orientation-correct single-link conditional law;
- [x] target-local and target-remote action decomposition;
- [x] exact remote-factor cancellation;
- [x] exact conditional total-variation influence;
- [x] plaquette-support locality and zero inactive influence;
- [x] exact oriented row sums;
- [x] canonical Dobrushin coefficient;
- [x] proof-carrying Dobrushin matrix;
- [x] active-neighbor coefficient majorant;
- [x] periodic four-dimensional bounds `d_active <= 18` and `m_shared <= 1` for side length at least three;
- [x] random-scan variation contraction;
- [x] Gibbs Hilbert realization;
- [x] Rayleigh and Poincare consequences;
- [x] normalized finite heat-bath Hamiltonian gap from `alpha < 1`;
- [x] compact-group finite-volume coercive, spectral, and resolvent packages under the strict coefficient hypothesis.

### Conditional continuum and OS constructors

- [x] common-carrier finite Wilson weak-limit framework;
- [x] tightness and Prokhorov subsequence constructor from explicit compactness data;
- [x] gauge and translation invariance transfer from equivariant interpolation;
- [x] gauge-invariant bounded-continuous observable algebra;
- [x] normalized positive continuum states and weak-star convergence;
- [x] finite-to-continuum reflection-positivity transfer interface;
- [x] OS null quotient, pre-Hilbert carrier, and Hilbert completion;
- [x] normalized vacuum and dense physical-state map;
- [x] strongly continuous contraction semigroup constructor;
- [x] right generator, right Hamiltonian, and graph closure;
- [x] nonnegative self-adjoint Hamiltonian under the stated symmetry hypotheses;
- [x] conditional vacuum-orthogonal Rayleigh gap transfer;
- [x] conditional zero-energy vacuum-line theorem;
- [x] conditional sub-gap eigenvector exclusion and real resolvent estimates.

These continuum results remain constructors from explicit hypotheses.

The physical model-specific hypotheses are not all discharged.

---

## Milestone 1 — reconcile the active proof carrier with `main`

Status: **required before mathematical promotion**

- [ ] rebase or transplant the carrier onto current `main`;
- [ ] remove the 169-commit backward divergence;
- [ ] reconcile files independently evolved on both histories;
- [ ] preserve the latest workflow improvements without duplicating obsolete CI logic;
- [ ] split generic functional analysis from Wilson-specific applications;
- [ ] split finite compact heat-bath theory from continuum OS theory;
- [ ] retain compile-smoke roots for each merge unit;
- [ ] obtain ordinary green CI after every structural split;
- [ ] refresh theorem indexes and public documentation after each promotion.

Definition of done:

The repository has one replayable dependency graph on `main`, and no authoritative `main` claim depends on an unmerged carrier branch.

---

## Milestone 2 — promote the explicit finite `Z2` theorem

Status: **implemented on the carrier; PR #302 remains open against `main`**

- [c] exact periodic oriented `Z2` coefficient bound;
- [c] explicit sufficient condition

```text
beta < log (19 / 17) / 2;
```

- [c] exponent-two unsigned proxy with matching Wilson action and one-link conditionals;
- [c] finite random-scan, Poincare, and native heat-bath Hamiltonian consequences;
- [c] exact finite-volume and side-length scope statement;
- [p] merge a reconciled and reviewable PR into `main`.

Definition of done:

The finite small-coupling theorem is replayed on `main` and remains explicitly separated from continuum `SU(N)` claims.

---

## Milestone 3 — promote native compact Haar heat-bath `L2` theory

Status: **integrated on the carrier through PRs #303--#309**

- [c] canonical single-link Haar coordinates and assembly;
- [c] exact one-link Gibbs conditional kernel;
- [c] stationarity and detailed balance;
- [c] `L2` conditional-expectation projection;
- [c] idempotence, orthogonality, and fluctuation decomposition;
- [c] random-scan positive contraction;
- [c] vacuum and vacuum-orthogonal sector decomposition;
- [c] compact-group Dobrushin Poincare inequality;
- [c] finite heat-bath Hamiltonian and restricted energy operator;
- [c] Lax--Milgram inverse and real resolvent estimates;
- [c] indexed uniform Dobrushin family;
- [c] uniform lower spectral enclosure and resolvent norm bound;
- [c] bundled finite-volume spectral-gap certificate;
- [ ] transplant the layer onto reconciled `main` in reviewable dependency order.

Definition of done:

The native Haar kernel and `L2` Hamiltonian replace abstract placeholders on `main`, with all measurability, probability-measure, and conditional-expectation assumptions explicit and replayed.

---

## Milestone 4 — promote coercive strong-limit transport

Status: **integrated on the carrier through PRs #310--#316**

### Identified common carrier

- [c] uniform quadratic lower bounds pass to a strong limit;
- [c] symmetry passes to the limit;
- [c] coercive energy form;
- [c] Lax--Milgram continuous linear equivalence;
- [c] all real shifts below the gap are invertible;
- [c] lower real spectral enclosure;
- [c] inverse-distance resolvent norm control.

### Varying Hilbert spaces

- [c] exact isometric identification bridge;
- [c] asymptotic approximation maps and isometric embeddings;
- [c] transport of finite compact Wilson gap data to a common carrier;
- [c] compact-Wilson-specific asymptotic strong-limit package;
- [ ] merge generic analysis before Wilson specialization.

Definition of done:

The common-carrier assumptions are stated independently from the physical interpolation theorem, and the generic strong-limit results are replayed on `main` before their Wilson wrappers.

---

## Milestone 5 — promote OS strong-resolvent convergence

Status: **integrated on the carrier through PR #328; CI repaired and green**

- [c] restrict the physical semigroup to the complete vacuum-orthogonal Hilbert sector;
- [c] prove coercivity and lower spectrum bounds for `I - T(t)`;
- [c] derive the eventual linear small-time defect estimate from a supplied positive mass slope;
- [c] define the bounded rescaled defect `t^(-1)(I - T(t))`;
- [c] obtain the common half-mass lower bound;
- [c] prove convergence on the canonical Hamiltonian core;
- [c] prove exact core resolvent-error identities;
- [c] prove dense range of the Hamiltonian core shift;
- [c] extend uniformly bounded pointwise convergence from a dense range;
- [c] construct the graph-closed continuum excitation resolvent for every `lambda < mass / 2`;
- [c] prove full strong-resolvent convergence on every excitation vector;
- [c] prove the equivalent norm-to-zero statement;
- [ ] promote the dependency chain to `main` without hiding the mass-slope or self-adjointness hypotheses.

Validation receipt:

```text
PR #328 final head:
  ba8b9e09856dd419e577a6861addd8f0893c7b56

PR Lean Fast Check:
  run 5151 — success
```

Definition of done:

The strong-resolvent theorem and its prerequisites are replayed on `main`, with the positive mass-slope and self-adjointness assumptions unchanged and visible.

---

## Milestone 6 — promote operator-graph convergence

Status: **integrated on the carrier through PRs #332--#364; CI green**

- [c] converge resolvent-selected graph pairs;
- [c] approximate every continuum Hamiltonian graph point;
- [c] establish graph-norm and sum-norm approximation variants;
- [c] prove closedness and range characterizations of the continuum graph;
- [c] identify sequential and filter-indexed graph limits;
- [c] handle approximate shifted equations;
- [c] handle varying right-hand sides and varying shifts;
- [c] define filter Painleve--Kuratowski inner and outer limits;
- [c] prove recovery and outer-limit containment;
- [c] identify exact shifted graphs with resolvent graph points;
- [c] prove ordinary operator-graph convergence without source or shift coordinates in the conclusion;
- [c] remove the auxiliary shift from the public theorem interface;
- [c] prove the canonical admissible small-time filter is nontrivial;
- [c] prove equality of both canonical Painleve--Kuratowski limits with the closed continuum Hamiltonian graph;
- [c] package canonical graph convergence with below-gap strong-resolvent convergence;
- [ ] promote the canonical package and its generic filter library to `main`.

Validation receipt:

```text
PR #364 head:
  67428df16f4057b7956f2b873a90c639572d070d

PR #364 merge commit on carrier:
  7f1dae659bef10ea1713d57d20a620d1065fbf1d

PR Lean Fast Check:
  run 5205 — success
```

Definition of done:

The canonical package is replayed from the root `MGAP4D` import surface on `main`, and its limitations are documented: no norm-resolvent conclusion, no unrestricted union-of-graphs closure, and no general spectral-projection convergence without further hypotheses.

---

## Milestone 7 — instantiate a concrete physical continuum family

Status: **open**

- [ ] choose a gauge-compatible Polish or distributional carrier;
- [ ] define explicit interpolation, smearing, or blocking maps;
- [ ] specify lattice spacing and physical volume trajectories;
- [ ] specify the bare or renormalized coupling trajectory;
- [ ] prove interpolation equivariance for gauge transformations;
- [ ] prove interpolation equivariance for time translations and reflection;
- [ ] construct a proper Sobolev-, Besov-, or gauge-invariant compactness functional;
- [ ] prove compactness of its sublevel sets;
- [ ] prove the required uniform moment or coercive estimate;
- [ ] establish tightness for the actual family;
- [ ] prove nontriviality of the resulting limit;
- [ ] identify the gauge quotient or gauge-fixing formulation.

Definition of done:

The weak-limit constructor is applied to explicit mathematical objects, and the limit is shown to be nontrivial rather than merely subsequential.

---

## Milestone 8 — derive a uniform physical positive gap

Status: **decisive open mathematical frontier**

The existing finite theorem generator accepts a strict Dobrushin or equivalent coercive certificate.

What remains is to prove a positive estimate uniformly for the actual physical approximation family and scaling trajectory.

Possible formal interfaces include:

- [ ] a uniform Dobrushin coefficient `alpha_n <= alpha_* < 1`;
- [ ] a uniform Poincare or log-Sobolev inequality;
- [ ] a block heat-bath or approximate tensorization estimate;
- [ ] a multiscale or polymer coercivity theorem;
- [ ] a reflection-positive transfer-operator contraction;
- [ ] a renormalization-group estimate producing a positive continuum mass slope;
- [ ] a Mosco or form-convergence theorem preserving the lower bound.

Every route must track lattice spacing, physical volume, coupling trajectory, gauge group, boundary conditions, observable sector, and the distinction between heat-bath Markov time and Euclidean time.

Definition of done:

A positive lower bound is proved for the actual physical family rather than stored as a structure field or assumed hypothesis.

---

## Milestone 9 — complete the instantiated OS reconstruction

Status: **open**

- [ ] prove reflection positivity for the full intended continuum observable class;
- [ ] prove the concrete real-time translation action and joint continuity;
- [ ] identify the continuum state with the weak limit of the lattice states;
- [ ] prove clustering or the required vacuum-sector uniqueness statement from physical data;
- [ ] construct a separating local gauge-invariant observable family;
- [ ] prove convergence and regularity of the required Schwinger distributions;
- [ ] complete Euclidean covariance;
- [ ] discharge the remaining Osterwalder--Schrader axioms;
- [ ] perform Wightman reconstruction;
- [ ] relate the reconstructed Hamiltonian to physical observables and units.

Definition of done:

The abstract OS data used by the Hamiltonian, resolvent, and graph-limit theorems are generated from the concrete continuum Yang--Mills construction.

---

## Milestone 10 — spectral consequences beyond the current carrier

Status: **future conditional analysis**

- [ ] derive convergence of bounded continuous functional calculi where justified;
- [ ] connect strong-resolvent convergence to semigroup convergence under the appropriate theorem;
- [ ] study isolated spectral projections under additional hypotheses;
- [ ] identify conditions preserving the vacuum projection and positive gap;
- [ ] formalize needed Mosco, graph, or form-convergence equivalences;
- [ ] connect excitation resolvents and graph limits to physical correlation decay.

Strong-resolvent and Painleve--Kuratowski graph convergence alone do not imply norm-resolvent convergence or convergence of every spectral projection.

---

## Milestone 11 — physical normalization and external review

Status: **open**

- [ ] keep the internal `33/20` lane separate from the physical mass parameter;
- [ ] derive any numerical mass from the instantiated Hamiltonian and scaling data;
- [ ] prove dimensional normalization and units;
- [ ] stabilize theorem names and import roots after carrier promotion;
- [ ] provide reproducible CI and local replay receipts;
- [ ] obtain independent mathematical review;
- [ ] distinguish machine replay, internal review, and external consensus in every public claim.

The value `33/20` remains an internal normalized audit value unless a separate physical derivation is completed.

## Immediate execution order

1. Reconcile `formal/real-hilbert-uniform-coercive-strong-limit` with current `main`.
2. Split the carrier into finite, generic functional-analytic, and continuum OS merge units.
3. Promote the explicit finite `Z2` and native compact Haar heat-bath layers.
4. Promote uniform finite spectral certificates and generic strong-limit transport.
5. Promote the OS defect, full strong-resolvent, graph-convergence, and canonical package layers.
6. Instantiate the physical carrier, interpolation, scaling trajectory, and nontrivial weak limit.
7. Prove a uniform positive physical gap for that family.
8. Apply the merged OS and operator-limit machinery to the instantiated continuum theory.
9. Complete reconstruction, physical normalization, and independent review.
