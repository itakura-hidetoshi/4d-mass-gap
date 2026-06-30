# MGAP4D Roadmap

This roadmap records the active proof-development path of `itakura-hidetoshi/4d-mass-gap`.

## Snapshot — 2026-06-30

```text
latest mathematical proof checkpoint on main:
  a80a75449a16d07889519c1823595c5244824583

latest merged mathematical proof PR:
  PR #300

current stacked frontier:
  PR #328
  head 540cc5848626fce2a69fff6948e14886e9591277

frontier base carrier:
  formal/real-hilbert-uniform-coercive-strong-limit
  a846a06aa286f4d0beb624bfd5e461653b797b58
```

The repository does not yet prove an unconditional interacting four-dimensional continuum Yang--Mills theory or a physical mass gap derived from a concrete continuum scaling trajectory.

Notation:

- `[x]` merged on `main`;
- `[~]` implemented on the stacked frontier but not on `main`;
- `[ ]` incomplete or not yet instantiated physically.

A merge inside the stacked branch family does not count as `[x]` unless the result has reached `main`.

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
- [x] compact-group finite-volume spectral, coercive, and resolvent packages under the strict coefficient hypothesis.

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

These continuum results remain constructors from explicit hypotheses. The physical model-specific hypotheses are not all discharged.

---

## Milestone 1 — merge the explicit finite `Z2` theorem

Status: **implemented in PR #302**

- [~] exact periodic oriented `Z2` coefficient bound;
- [~] explicit sufficient condition

```text
beta < log (19 / 17) / 2;
```

- [~] exponent-two unsigned proxy with matching Wilson action and one-link conditionals;
- [~] finite random-scan, Poincare, and native heat-bath Hamiltonian consequences;
- [~] exact finite-volume and side-length scope statement.

Definition of done:

The PR is rebased onto `main`, ordinary CI is green, the finite small-coupling scope is retained, and the theorem is merged without being described as a continuum Yang--Mills result.

---

## Milestone 2 — merge the native compact Haar heat-bath theory

Status: **implemented across PRs #303--#309**

- [~] canonical single-link Haar coordinates and assembly;
- [~] exact one-link Gibbs conditional kernel;
- [~] stationarity and detailed balance;
- [~] `L2` conditional-expectation projection;
- [~] idempotence, orthogonality, and fluctuation decomposition;
- [~] random-scan positive contraction;
- [~] vacuum and vacuum-orthogonal sector decomposition;
- [~] compact-group Dobrushin Poincare inequality;
- [~] finite heat-bath Hamiltonian and restricted energy operator;
- [~] Lax--Milgram inverse and real resolvent estimates;
- [~] indexed uniform Dobrushin family;
- [~] uniform lower spectral enclosure and resolvent norm bound;
- [~] bundled finite-volume spectral-gap certificate.

Definition of done:

The native Haar kernel and `L2` Hamiltonian replace abstract placeholders on `main`, with all measurability, probability-measure, and conditional-expectation assumptions explicit and replayed.

---

## Milestone 3 — merge coercive strong-limit transport

Status: **implemented across PRs #310--#316**

### Identified common carrier

- [~] uniform quadratic lower bounds pass to a strong limit;
- [~] symmetry passes to the limit;
- [~] coercive energy form;
- [~] Lax--Milgram continuous linear equivalence;
- [~] all real shifts below the gap are invertible;
- [~] lower real spectral enclosure;
- [~] sharp inverse-distance resolvent norm control.

### Varying Hilbert spaces

- [~] exact isometric identification bridge;
- [~] asymptotic approximation maps and isometric embeddings;
- [~] transport of finite compact Wilson gap data to a common carrier;
- [~] compact-Wilson-specific asymptotic strong-limit package.

Definition of done:

The branch stack is rebased onto `main`, the common-carrier assumptions are stated independently from the physical interpolation theorem, and the generic strong-limit results are merged before their Wilson specialization.

---

## Milestone 4 — merge the OS semigroup-defect spectrum layer

Status: **implemented across PRs #317--#321**

- [~] restrict the physical semigroup to the complete vacuum-orthogonal Hilbert sector;
- [~] prove coercivity and lower spectrum bounds for `I - T(t)`;
- [~] expose the common-carrier Wilson defect spectrum API;
- [~] derive one strict positive Euclidean time from a positive mass slope;
- [~] prove an eventual linear small-time defect estimate;
- [~] define the bounded rescaled defect `t^(-1)(I - T(t))`;
- [~] obtain the time-independent half-mass lower bound;
- [~] prove the corresponding resolvent half-line and norm estimates.

Definition of done:

The mass-slope input remains visible in every public theorem statement, and no defect-spectrum result is described as a derivation of the physical mass slope.

---

## Milestone 5 — merge graph-core and full strong-resolvent convergence

Status: **implemented through PR #328**

- [~] define the canonical vacuum-orthogonal right-Hamiltonian core;
- [~] prove rescaled OS defects converge to the graph-closed Hamiltonian on the core;
- [~] prove exact resolvent-error identities on shifted core vectors;
- [~] prove resolvent convergence on the core-shift range;
- [~] prove uniform resolvent norm bounds;
- [~] extend uniformly bounded pointwise convergence from a dense range;
- [~] extract vacuum-orthogonal graph-core approximations;
- [~] prove dense range of the Hamiltonian core shift;
- [~] construct the graph-closed continuum excitation resolvent at every `lambda < mass / 2`;
- [~] prove full strong-resolvent convergence on every excitation Hilbert-space vector;
- [~] prove the equivalent norm-to-zero statement.

Current receipt:

```text
PR #328 head:
  540cc5848626fce2a69fff6948e14886e9591277

PR Lean Fast Check:
  run 5141, in progress at the 2026-06-30 snapshot
```

Definition of done:

CI is green, the stacked history is rebased and decomposed, and the theorem reaches `main` with the positive mass-slope and self-adjointness hypotheses unchanged.

---

## Milestone 6 — reconcile the frontier with `main`

Status: **required before mathematical promotion**

Relative to the latest mathematical checkpoint `a80a7544…`, the frontier has diverged:

```text
frontier relative to checkpoint:
  ahead 237
  behind 157
  merge base 929e20583ae368475d4bedb65c060c2d3c4c0fff
```

Required work:

- [ ] rebase the frontier onto the current `main` head;
- [ ] resolve duplicate or independently evolved theorem files;
- [ ] split generic functional analysis from Wilson-specific applications;
- [ ] split finite compact heat-bath theory from continuum OS theory;
- [ ] retain compile-smoke roots for each merge unit;
- [ ] run ordinary branch-wide CI after every structural split;
- [ ] update theorem indexes and documentation after each mathematical merge.

Definition of done:

The repository has one replayable dependency graph on `main`, and no authoritative theorem claim depends on an unmerged stacked branch.

---

## Milestone 7 — instantiate a concrete physical continuum family

Status: **open**

- [ ] choose a gauge-compatible Polish or distributional carrier;
- [ ] define explicit interpolation, smearing, or blocking maps;
- [ ] specify lattice spacing and physical volume trajectories;
- [ ] specify the bare or renormalized coupling trajectory;
- [ ] prove interpolation equivariance for gauge transformations;
- [ ] prove interpolation equivariance for lattice-time translations and reflection;
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

What remains is to prove such a positive estimate uniformly for the actual physical approximation family and scaling trajectory.

Possible formal interfaces include:

- [ ] a uniform Dobrushin coefficient `alpha_n <= alpha_* < 1`;
- [ ] a uniform Poincare or log-Sobolev inequality;
- [ ] a block heat-bath or approximate tensorization estimate;
- [ ] a multiscale or polymer coercivity theorem;
- [ ] a reflection-positive transfer-operator contraction;
- [ ] a renormalization-group estimate producing a positive continuum mass slope;
- [ ] a Mosco or form-convergence theorem preserving the lower bound.

Every route must track:

```text
lattice spacing
physical volume
coupling trajectory
gauge group
boundary conditions
observable sector
heat-bath time versus Euclidean time.
```

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

The abstract OS data used by the merged Hamiltonian and resolvent theorems are generated from the concrete continuum Yang--Mills construction.

---

## Milestone 10 — spectral consequences beyond the current frontier

Status: **next functional-analytic layer after PR #328**

- [ ] derive strong convergence of bounded functional calculi where justified;
- [ ] connect strong-resolvent convergence to semigroup convergence;
- [ ] study stability of isolated spectral projections under additional hypotheses;
- [ ] identify conditions preserving the vacuum projection and positive gap in the limit;
- [ ] formalize any required Mosco, graph, or form convergence equivalences;
- [ ] connect the excitation resolvent to physical correlation decay.

Strong-resolvent convergence alone does not imply norm-resolvent convergence or convergence of every spectral projection.

---

## Milestone 11 — physical normalization and external audit

Status: **open**

- [ ] keep the internal `33/20` lane separate from the physical mass parameter;
- [ ] derive any numerical mass from the instantiated Hamiltonian and scaling data;
- [ ] prove dimensional normalization and units;
- [ ] stabilize theorem names and import roots;
- [ ] provide reproducible CI and local replay receipts;
- [ ] obtain independent mathematical review;
- [ ] distinguish machine replay, internal review, and external consensus in every public claim.

The value `33/20` remains an internal normalized audit value unless a separate physical derivation is completed.

## Immediate execution order

1. Complete PR #328 CI.
2. Rebase and decompose the stacked frontier against current `main`.
3. Merge PR #302's finite explicit theorem.
4. Merge the native compact Haar heat-bath and uniform finite spectral layers.
5. Merge the generic strong-limit transport before the Wilson specialization.
6. Merge the OS defect, graph-core, and full strong-resolvent layers.
7. Instantiate the physical carrier, interpolation, scaling, and nontrivial weak limit.
8. Prove a uniform positive physical gap for that family.
9. Apply the merged OS and resolvent machinery to the instantiated continuum theory.
10. Complete reconstruction, physical normalization, and external review.
