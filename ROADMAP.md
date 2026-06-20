# MGAP4D Roadmap

This roadmap records the active proof-development path of `itakura-hidetoshi/4d-mass-gap`.

## Snapshot — 2026-06-20

```text
main head: 017ad8ea96346100af31af114f69380c6194d8e1 (PR #290, docs)
latest merged proof checkpoint: 59c5780e1efd9e0035aad9bb8c65ff752f5b89dc (PR #288)
active proof PRs: #289 and #282
```

The repository does not yet prove an unconditional continuum Yang--Mills theory or physical mass gap.

Notation:

- `[x]` merged on `main`;
- `[~]` implemented in an open PR but not on `main`;
- `[ ]` incomplete.

## Completed on `main`

### 1. Finite Gibbs and Hamiltonian spine

- [x] finite Wilson Gibbs PMF and exact single-link conditional laws;
- [x] Gibbs expectation, variance, and heat-bath Dirichlet form;
- [x] conditional projection `P_e` and fluctuation projection `Q_e`;
- [x] detailed balance, symmetry, orthogonality, and weighted Pythagoras;
- [x] concrete finite Gibbs Hilbert realization and normalized vacuum;
- [x] heat-bath Hamiltonian `H_HB = sum_e Q_e`;
- [x] exact identity `H_HB = |E| (I - P_scan)`.

### 2. Canonical Dobrushin-to-Rayleigh theorem

PRs #267--#272 prove

```text
exact conditional-TV influence
  -> canonical coefficient alpha_can
  -> variation contraction
  -> random-scan iterate contraction
  -> centered fixed-point triviality
  -> eigenvalue control
  -> Gibbs-Hilbert spectral lift
  -> centered Rayleigh contraction
  -> finite Hamiltonian gap.
```

- [x] exact off-diagonal influence and zero diagonal;
- [x] exact row sums, canonical coefficient, and minimality;
- [x] centered spectral and Rayleigh consequences;
- [x] automatic finite gap consequences from `alpha_can < 1`.

The missing input is now a physically relevant uniform strict estimate, not a separate Rayleigh theorem.

### 3. Plaquette support and periodic geometry

- [x] target-local / target-remote decomposition;
- [x] remote-factor cancellation in normalized conditionals;
- [x] exact zero influence outside plaquette support;
- [x] `alpha_can <= d_active * eta_active`;
- [x] shared-plaquette localization;
- [x] normalized-exponential bound

```text
eta_active <=
  (exp (2 * beta * m_shared * E_max) - 1) /
  (exp (2 * beta * m_shared * E_max) + 1);
```

- [x] signed periodic four-dimensional geometry;
- [x] `d_active <= 18` and `m_shared <= 1` for side length `n >= 3`;
- [x] orientation-correct finite Wilson system;
- [x] periodic oriented `Z2` instance.

---

## Milestone 1 — oriented finite conditional/influence bridge

Status: **in progress in PR #289**

- [~] physical-link replacement and agreement away from the source link;
- [~] signed holonomy congruence and non-neighbor locality;
- [~] oriented target-local / target-remote decomposition;
- [ ] rebase and merge PR #289;
- [ ] construct the oriented exact conditional law;
- [ ] prove normalized remote-factor cancellation;
- [ ] construct oriented canonical influence;
- [ ] connect it to the merged Dobrushin/Rayleigh API.

Definition of done:

```text
The physical-link oriented Wilson system generates exact conditionals,
canonical influence, and finite Hamiltonian consequences directly.
```

## Milestone 2 — explicit periodic `Z2` finite theorem

- [ ] package `E_max = 1`;
- [ ] insert `d_active <= 18` and `m_shared <= 1`;
- [ ] derive `eta_active <= (exp (2*beta)-1)/(exp (2*beta)+1)`;
- [ ] derive a sufficient strict condition `18 * eta_active < 1`;
- [ ] generate centered-Rayleigh and finite Hamiltonian-gap consequences;
- [ ] state the exact finite parameter range.

This is a finite-volume small-`beta` result, not a continuum weak-coupling theorem.

---

## Milestone 3 — stabilize the concrete compact `SU(N)` probability lane

Status: **substantially implemented in PR #282**

### Finite-volume input

- [~] orientation-correct compact gauge Wilson system;
- [~] product Haar probability measure and Gibbs tilt;
- [~] finite-volume gauge invariance;
- [~] periodic four-dimensional geometry bridge;
- [~] exact plaquette count `6 * L^4`;
- [~] standard `SU(N)` Wilson energy `1 - Re(trace U)/N`;
- [~] continuity, conjugation invariance, and `0 <= E_W <= 2`;
- [~] reciprocal-plaquette normalized action bound `<= 2`.

### Weak-limit and observable spine

- [~] varying finite lattice laws embedded into one fixed Polish carrier;
- [~] lattice spacing to zero and physical volume to infinity;
- [~] proper coercive-functional interface;
- [~] action domination, moment control, Markov tails, and tightness;
- [~] Prokhorov subsequence and physical weak-limit package;
- [~] bounded-continuous expectation convergence;
- [~] compatible continuum gauge-symmetry transfer;
- [~] invariant events, observable laws, correlations, and finite n-point moments;
- [~] real algebra of gauge-invariant observables;
- [~] positive continuous states and weak-star convergence.

### Integration tasks

- [ ] complete validation of the newest Hilbert-kernel/OS files;
- [ ] restore the ordinary main-compatible PR workflow after diagnostics;
- [ ] audit assumptions and generated instances;
- [ ] rebase onto current `main` and resolve overlap with PR #289;
- [ ] merge only after ordinary PR Lean Fast Check is green.

---

## Milestone 4 — instantiate the physical weak-limit inputs

PR #282 supplies the constructor, but the decisive analytic objects remain open.

- [ ] choose a gauge-compatible distributional carrier;
- [ ] define explicit interpolation, blocking, or smearing maps;
- [ ] specify the physical lattice spacing, volume, and coupling trajectory;
- [ ] justify the renormalized `beta_n` scaling;
- [ ] construct a proper Sobolev/Besov-type functional `Phi`;
- [ ] prove compactness of its sublevels;
- [ ] prove a uniform coercive estimate of the form

```text
Phi(interpolate_n(A)) <= controlled renormalized Wilson observable;
```

- [ ] derive tightness for the actual physical scaling family;
- [ ] state the gauge quotient or gauge-fixing formulation explicitly.

Definition of done: the weak-limit theorem is instantiated by concrete physical objects rather than abstract parameters.

---

## Milestone 5 — concrete OS reflection positivity

Status: **generic transfer implemented in PR #282; concrete `SU(N)` data incomplete**

The branch factors the proof into

```text
positive-time observable algebra and reflection
  + exact half-lattice measure/action splitting
  + Peter--Weyl Hilbert-feature factorization
  -> finite reflection positivity
  -> weak-star limit transfer
  -> continuum reflection-positive state.
```

Implemented in PR #282:

- [~] weak-star state convergence;
- [~] sequential closedness of reflection positivity;
- [~] finite Wilson OS-to-physical-state bridge interfaces;
- [~] kernel-quadratic and Hilbert-feature certificate interfaces;
- [~] terminal continuum OS-positive state package.

Still required:

- [ ] define the actual positive-time physical observable algebra and reflection;
- [ ] construct the periodic `SU(N)` half-lattice decomposition;
- [ ] prove exact Haar-measure and Wilson-action splitting;
- [ ] prove the required nonnegative Wilson character coefficients;
- [ ] construct the Peter--Weyl feature and integrability proof;
- [ ] identify the abstract quadratic form with the actual Gibbs reflection form;
- [ ] replay the complete concrete finite-to-continuum route.

---

## Milestone 6 — nontrivial continuum theory and full OS axioms

- [ ] prove nontriviality and interacting character;
- [ ] prove uniqueness or characterize subsequence/phase selection;
- [ ] construct a separating gauge-invariant observable family;
- [ ] prove convergence of the required Schwinger distributions;
- [ ] prove Euclidean covariance, regularity, and clustering;
- [ ] establish the remaining Osterwalder--Schrader axioms;
- [ ] align the probability-measure and observable-algebra formulations.

---

## Milestone 7 — continuum-relevant uniform gap mechanism

Single-link Dobrushin control may be too restrictive. Candidate routes are:

- [ ] block heat-bath dynamics or block Dobrushin estimates;
- [ ] approximate tensorization;
- [ ] multiscale/polymer estimates;
- [ ] reflection-positive transfer estimates;
- [ ] renormalization-group coercivity;
- [ ] another explicit scale-uniform mechanism.

Every route must track lattice spacing, physical volume, coupling, gauge group, and boundary conditions; distinguish heat-bath time from physical Euclidean time; and avoid assuming the desired gap.

---

## Milestone 8 — OS reconstruction and physical mass gap

- [ ] construct the OS pre-Hilbert space and null quotient;
- [ ] complete the physical Hilbert space and vacuum;
- [ ] construct the time-translation semigroup and self-adjoint generator;
- [ ] derive the physical normalization independently of `exactGapValueReal`;
- [ ] identify the vacuum-orthogonal sector;
- [ ] transfer continuum decay/coercivity to a positive spectral lower bound;
- [ ] prove nonzero observable spectral weight;
- [ ] obtain independent replay and specialist review.

---

## Exact `33/20` lane

Status: **internal normalization/audit carrier, not an independently derived physical value**

- [x] `33/20` is transported through internal PVM/spectral and R6--R7 interfaces;
- [x] internal, finite heat-bath, and physical layers are documented as distinct;
- [ ] derive the physical normalization independently;
- [ ] construct the continuum Hamiltonian independently;
- [ ] derive its spectral infimum and observable weight;
- [ ] prove, rather than preload, any equality with `33/20`;
- [ ] obtain external review of any exact-value claim.

## Release gates

### Source gate

- [ ] fresh-clone `bash scripts/check.sh` and `lake build`;
- [ ] ordinary workflow restored with no temporary diagnostics;
- [ ] new aggregate imports are in replay coverage;
- [ ] documentation claims have theorem/file anchors;
- [ ] placeholder inventory is current;
- [ ] stale or overtaken PRs are closed, rebased, or marked.

### Mathematical gate

- [ ] concrete carrier, interpolation, and renormalized scaling;
- [ ] concrete coercive compactness estimate;
- [ ] concrete periodic `SU(N)` OS certificate;
- [ ] nontrivial interacting continuum law;
- [ ] full OS reconstruction;
- [ ] continuum-relevant uniform gap estimate;
- [ ] physical Hamiltonian normalization and positive gap.

### External-claim gate

- [ ] independent replay and dependency audit;
- [ ] mathematical-physics specialist review;
- [ ] no circular use of the target gap or numerical value;
- [ ] public wording matches the theorem boundary.

## Execution order

```text
finish PR #282 validation and restore the ordinary workflow
  -> instantiate concrete SU(N) half-lattice/Peter--Weyl data
  -> merge the concrete finite-law and weak-limit spine
  -> choose the physical carrier and interpolation
  -> prove the actual coercive compactness estimate
  -> establish nontriviality and the remaining OS axioms
  -> develop a continuum-relevant uniform gap mechanism
  -> perform OS reconstruction and physical normalization
  -> prove the physical Hamiltonian mass gap
  -> independent validation.

parallel finite lane:
PR #289 oriented locality
  -> oriented conditionals and canonical influence
  -> explicit periodic Z2 finite strict-coefficient theorem.
```
