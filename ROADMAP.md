# MGAP4D Roadmap

This roadmap records the active proof-development path of `itakura-hidetoshi/4d-mass-gap`.

## Snapshot — 2026-06-28

```text
main head before this documentation update:
  923d47c997a9b1b59cfb6a87adc30fdc4fdeee9d

latest merged proof checkpoint:
  PR #298 — oriented canonical Dobrushin influence

active physical branch:
  PR #282
  head 509cfbe825ee635940b9fe5728fe1d437a376356

stacked operator-state branch:
  PR #299
```

The repository does not yet prove an unconditional interacting continuum Yang--Mills theory or an independently derived physical mass gap.

Notation:

- `[x]` merged on `main`;
- `[~]` implemented in an open PR but not on `main`;
- `[ ]` incomplete.

## Completed on `main`

### Finite Gibbs and Hamiltonian spine

- [x] finite Wilson Gibbs PMF and exact single-link conditionals;
- [x] Gibbs expectation, variance, and heat-bath Dirichlet form;
- [x] conditional projection `P_e` and fluctuation projection `Q_e`;
- [x] detailed balance, Gibbs symmetry, orthogonality, and weighted Pythagoras;
- [x] concrete finite Gibbs Hilbert realization and normalized vacuum;
- [x] heat-bath Hamiltonian `H_HB = sum_e Q_e`;
- [x] exact identity `H_HB = |E| (I - P_scan)`.

### Legacy canonical Dobrushin-to-Rayleigh spine

- [x] exact conditional-TV influence and zero diagonal;
- [x] exact row sums and canonical coefficient `alpha_can`;
- [x] variation and normalized random-scan contraction;
- [x] centered fixed-point triviality and eigenvalue control;
- [x] Gibbs-Hilbert spectral lift;
- [x] centered Rayleigh contraction;
- [x] finite Hamiltonian-gap consequences from `alpha_can < 1`.

### Plaquette locality and periodic geometry

- [x] target-local / target-remote Wilson-action decomposition in the legacy interface;
- [x] exact remote-factor cancellation;
- [x] exact zero influence outside plaquette support;
- [x] `alpha_can <= d_active * eta_active`;
- [x] normalized-exponential TV majorant;
- [x] signed periodic four-dimensional geometry;
- [x] `d_active <= 18` and `m_shared <= 1` for side length `n >= 3`;
- [x] orientation-correct finite Wilson system;
- [x] periodic oriented `Z2` instance.

### Orientation-correct conditional and influence spine

Merged PRs #289 and #293--#298 complete the following layers:

- [x] physical-link replacement and agreement away from the source link;
- [x] signed plaquette-holonomy locality;
- [x] oriented target-local / target-remote action decomposition;
- [x] exact oriented single-link conditional PMF;
- [x] local/remote Boltzmann factorization;
- [x] exact partition-function factorization and remote cancellation;
- [x] `finiteNormalizedExp` representation;
- [x] conditional-TV control from mutual exponential ratios;
- [x] local-action-oscillation TV bound;
- [x] exact oriented canonical influence;
- [x] nonnegativity and exact zero diagonal;
- [x] sharp active-influence exponential-ratio bound.

---

## Milestone 1 — close the oriented Dobrushin coefficient bridge

Status: **next finite `main` milestone**

- [ ] prove coefficient-level zero influence for inactive sources in the oriented interface;
- [ ] define exact oriented row sums;
- [ ] define the oriented canonical coefficient;
- [ ] prove the active-neighbor row-sum bound;
- [ ] transport the periodic bounds `d_active <= 18` and `m_shared <= 1` into the oriented coefficient;
- [ ] connect the oriented coefficient to the merged random-scan/Rayleigh/Hamiltonian API;
- [ ] add one aggregate compile-smoke import.

Definition of done:

```text
orientation-correct physical-link Wilson conditionals
  -> exact oriented canonical coefficient
  -> strict coefficient hypothesis
  -> centered Rayleigh contraction
  -> finite heat-bath Hamiltonian gap.
```

## Milestone 2 — explicit periodic `Z2` finite theorem

- [ ] package the concrete `Z2` plaquette-energy bound;
- [ ] insert `d_active <= 18` and `m_shared <= 1`;
- [ ] derive the explicit active-influence majorant;
- [ ] state a sufficient strict parameter condition;
- [ ] generate centered-Rayleigh and finite Hamiltonian-gap consequences;
- [ ] state the exact finite-volume scope and side-length restriction.

This milestone is a finite small-coupling theorem.

It is not a continuum weak-coupling or asymptotic-freedom theorem.

---

## Milestone 3 — stabilize and decompose PR #282

Status: **large open branch, not merge-ready**

Current branch snapshot:

```text
head: 509cfbe825ee635940b9fe5728fe1d437a376356
commits: 1315
changed files: 334
additions/deletions: +42411/-0
```

Current-head workflows are queued:

- [~] ordinary PR Lean Fast Check run 4698;
- [~] Temporary Concrete Wilson OS Boundary Gap Check run 113;
- [~] Temporary Exponential Boundary Poincare Check run 30.

Required stabilization:

- [ ] obtain ordinary branch-wide green CI;
- [ ] remove temporary diagnostic workflows;
- [ ] audit aggregate imports and compile-smoke roots;
- [ ] rebase on the updated oriented finite `main` lane;
- [ ] split the 334-file branch into mathematically reviewable merge units;
- [ ] merge only replayable layers with explicit claim boundaries.

Recommended split order:

1. finite compact `SU(N)` probability and symmetry layer;
2. concrete finite even-periodic reflection-positivity layer;
3. weak-limit, observable, and weak-star state layer;
4. OS Hilbert and semigroup layer;
5. closed Hamiltonian and resolvent layer;
6. conditional boundary-gap transfer layer.

---

## Milestone 4 — merge the concrete finite `SU(N)` reflection-positive theory

Status: **implemented in PR #282**

### Finite probability and symmetry

- [~] positive-physical-link compact Wilson system;
- [~] normalized product-Haar probability measure;
- [~] Wilson Gibbs tilt;
- [~] finite gauge invariance;
- [~] arbitrary periodic translation invariance;
- [~] integer temporal translations;
- [~] exact periodic plaquette count `6 * L^4`;
- [~] standard `SU(N)` Wilson energy and `0 <= E_W <= 2`.

### Reflection positivity

- [~] even-periodic time reflection;
- [~] positive, negative, and fixed-boundary edge sectors;
- [~] boundary/open-half coordinate equivalences;
- [~] Haar product and pushforward factorization;
- [~] exact Wilson Gibbs density sector factorization;
- [~] temporal and spatial crossing decomposition;
- [~] local Wilson positive-semidefinite kernels;
- [~] RKHS/Bochner-Gram representation;
- [~] bounded-continuous finite Gibbs reflection positivity.

Definition of done: these finite theorems are merged on `main`, replay with ordinary CI, and no longer depend on temporary workflows.

---

## Milestone 5 — instantiate the physical weak-limit construction

PR #282 supplies a general constructor, but the final physical analytic data remain open.

- [ ] choose a gauge-compatible distributional carrier;
- [ ] define explicit interpolation, smearing, or blocking maps;
- [ ] specify lattice spacing, physical volume, and coupling trajectory;
- [ ] justify the renormalized `beta_n` scaling;
- [ ] construct a proper Sobolev/Besov-type functional;
- [ ] prove compactness of its sublevels;
- [ ] prove the uniform coercive interpolation estimate;
- [ ] establish tightness for the intended physical family;
- [ ] state the gauge quotient or gauge-fixing formulation explicitly;
- [ ] prove nontriviality of the resulting weak limit.

Definition of done: the weak-limit theorem is instantiated by concrete physical objects rather than abstract parameters.

---

## Milestone 6 — instantiate continuum time and reflection covariance

The branch now contains the correct constructor pattern:

```text
integer lattice translations
  + latticeTime(n,k) = k * latticeSpacing(n)
  + latticeSpacing(n) -> 0
  -> floor-based dense temporal approximation
  + joint continuity
  -> continuum real-time invariance.
```

Still required for the selected physical carrier:

- [ ] construct the real-parameter physical time action;
- [ ] prove joint continuity;
- [ ] prove interpolation equivariance at lattice times;
- [ ] prove gauge/time commutation;
- [ ] construct the continuum reflection;
- [ ] prove reflection/time inversion;
- [ ] prove positive-time observable restriction;
- [ ] identify the OS state with the continuum weak-star state;
- [ ] prove observable-state strong continuity.

Definition of done: the physical continuum state carries the concrete reflection and strongly continuous Euclidean-time semigroup used by OS reconstruction.

---

## Milestone 7 — prove the scale-uniform Wilson boundary gap estimate

This is the decisive current mass-gap frontier.

The preferred direct interface is:

```text
mass > 0,

(1 - exp (-mass * t)) * ||v||^2
  <= ||v||^2 - ||K_(n,t) v||^2
```

uniformly in the approximation scale.

Alternative equivalent routes include:

- [ ] a factorization `K_(n,t) = S_(n,t) o A_(n,t)` with a strict operator-norm product bound;
- [ ] block heat-bath or block Poincaré estimates;
- [ ] approximate tensorization;
- [ ] multiscale or polymer estimates;
- [ ] reflection-positive transfer estimates;
- [ ] renormalization-group coercivity.

Every route must track lattice spacing, physical volume, coupling, gauge group, boundary conditions, and the distinction between heat-bath time and Euclidean time.

Definition of done: a positive `mass` and the required estimate are proved for the actual physical approximation family, rather than stored in a certificate field.

---

## Milestone 8 — discharge the conditional continuum gap theorem

Status: **the theorem-generating closure is implemented in PR #282**

From the boundary-gap certificate and strong continuity, PR #282 derives:

- [~] a continuum half-time OS quadratic gap certificate;
- [~] a graph-closed nonnegative Hamiltonian;
- [~] self-adjointness;
- [~] the vacuum-orthogonal Rayleigh lower bound with exact mass;
- [~] zero-energy eigenspace equal to the normalized vacuum line;
- [~] exclusion of nonzero eigenvectors in `(0, mass)`.

The theorem is conditional until Milestones 5--7 instantiate its inputs.

Definition of done: the actual physical approximation family supplies every field of the certificate and the resulting Hamiltonian theorem is stated without an unproved positive-gap hypothesis.

---

## Milestone 9 — complete the continuum theory and reconstruction

- [ ] prove interacting nontriviality;
- [ ] prove uniqueness or characterize subsequence/phase selection;
- [ ] construct a separating local gauge-invariant observable family;
- [ ] prove convergence and regularity of the required Schwinger distributions;
- [ ] prove full Euclidean covariance;
- [ ] prove clustering;
- [ ] complete the Osterwalder--Schrader axioms;
- [ ] perform the corresponding Wightman reconstruction;
- [ ] construct the relevant local operator algebras;
- [ ] relate the reconstructed Hamiltonian to physical observables and units.

PR #299's vacuum operator vector state is an additive step, not a substitute for these tasks.

---

## Milestone 10 — numerical normalization and external audit

- [ ] keep the internal `33/20` dependency lane separate from the physical mass parameter;
- [ ] derive any numerical mass value from the instantiated physical Hamiltonian and scaling data;
- [ ] prove dimensional normalization and units;
- [ ] provide stable theorem indexes and replay receipts;
- [ ] obtain independent mathematical review;
- [ ] distinguish machine replay, internal audit, and external consensus in every public statement.

The value `33/20` remains an internal normalized audit value unless a separate physical derivation is completed.

## Immediate execution order

1. Close the oriented coefficient-to-Hamiltonian bridge on `main`.
2. Package the explicit periodic `Z2` finite theorem.
3. Stabilize and split PR #282.
4. Merge the finite `SU(N)` probability and reflection-positive layers.
5. Instantiate the carrier, scaling, temporal/reflection covariance, and strong continuity.
6. Prove the scale-uniform boundary gap estimate.
7. Apply the existing conditional Hamiltonian-gap closure.
8. Complete nontriviality, OS/Wightman reconstruction, physical normalization, and external review.
