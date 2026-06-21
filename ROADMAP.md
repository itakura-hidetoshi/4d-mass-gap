# MGAP4D Roadmap

This roadmap records the active proof-development path of `itakura-hidetoshi/4d-mass-gap`.

## Snapshot — 2026-06-21

```text
main head: 42223c9a87dc1a8474be95d37abf51299578e9c0
latest merged proof checkpoint: PR #288, 59c5780e1efd9e0035aad9bb8c65ff752f5b89dc
latest merged documentation checkpoint: PR #291, d89e8375ab1c5b1dd028829901bc32f92060e0a0
active proof PRs: #289 and #282
PR #282 head: 592f3068bbb7f00b3a803ea75a3ed402d6674e3a
```

The repository does not yet prove an unconditional continuum Yang--Mills theory, a reconstructed physical Hamiltonian, or a physical mass gap.

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
- [x] automatic finite-gap consequences from `alpha_can < 1`.

The missing quantitative input is a physically relevant scale-uniform strict estimate, not a separate Rayleigh theorem.

### 3. Plaquette support and periodic oriented geometry

- [x] target-local / target-remote decomposition in the legacy finite interface;
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

## Milestone 1 — finish the oriented finite conditional/influence bridge

Status: **in progress in PR #289 and follow-up work**

- [~] physical-link replacement and agreement away from the source link;
- [~] signed holonomy congruence and non-neighbor locality;
- [~] oriented target-local / target-remote decomposition;
- [ ] rebase and merge PR #289;
- [ ] construct the oriented exact conditional law;
- [ ] prove normalized remote-factor cancellation in the oriented interface;
- [ ] construct oriented canonical influence;
- [ ] connect it to the merged Dobrushin/Rayleigh/Hamiltonian API.

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

### Stabilization tasks

- [ ] complete the ordinary PR Lean Fast Check on the current head;
- [ ] remove all temporary diagnostic workflows;
- [ ] audit assumptions, generated instances, and aggregate imports;
- [ ] rebase onto current `main` and resolve overlap with PR #289 where necessary;
- [ ] split or merge only replayable, reviewable layers.

Definition of done: the concrete finite-law, weak-limit, symmetry, observable, and state spine is on `main` with the ordinary workflow green.

---

## Milestone 4 — complete the exact Wilson RKHS/kernel layer

Status: **implemented in PR #282, pending final aggregate validation**

### Kernel and feature construction

- [~] standard `SU(N)` Wilson relative crossing kernel;
- [~] positive-semidefinite/RKHS certificate;
- [~] exact unit diagonal `K_beta(g,g) = 1`;
- [~] exact one-plaquette feature norm `= 1`;
- [~] exact pulled-back local crossing-feature norm `= 1`;
- [~] finite completed-tensor-product feature;
- [~] exact global feature norm `= 1`;
- [~] finite Gram and Hilbert-feature identities.

### Measurability and integrability

- [~] local feature strong measurability interface;
- [~] global finite-product feature measurability from local factors;
- [~] weighted feature measurability from scalar amplitude and global feature;
- [~] bounded integrability constructor from finite measure, strong measurability, and a uniform norm bound;
- [~] reduction of the weighted-feature norm bound to a scalar amplitude bound.

### OS constructors

- [~] bounded-local-kernel finite reflection-positivity constructor;
- [~] amplitude-bounded local-kernel constructor;
- [~] factored amplitude/local-feature measurability constructor;
- [~] approximating weak-star reflection positivity;
- [~] continuum weak-star reflection positivity by sequential closure.

Remaining:

- [ ] ensure all newest files are included in ordinary aggregate replay;
- [ ] remove redundant earlier interfaces now subsumed by exact unit-norm results;
- [ ] document the minimal assumptions of the final constructor.

Definition of done: the exact Wilson kernel-to-feature-to-integrability-to-OS route compiles as one ordinary aggregate import with no temporary diagnostics.

---

## Milestone 5 — concrete even-periodic half-lattice and crossing product

Status: **substantially implemented in PR #282, but the actual Gibbs-form identification remains incomplete**

### Even-periodic geometry

- [~] even periodic time reflection;
- [~] crossing-plaquette labels and finite list;
- [~] positive-half holonomy interfaces;
- [~] product of local Wilson crossing kernels;
- [~] half-lattice/Peter--Weyl and local-kernel product packages.

### Required model-specific identities

- [ ] identify the actual positive-time observable algebra and reflection used by the physical state;
- [ ] prove the exact periodic `SU(N)` half-lattice action decomposition;
- [ ] prove the exact crossing-kernel identity for the actual Wilson Gibbs weight;
- [ ] verify Haar-measure factorization with reflection-fixed variables treated correctly;
- [ ] identify the abstract pullback form with the actual Gibbs reflection form;
- [ ] replay the entire finite-to-continuum reflection-positive route.

Definition of done:

```text
The actual periodic SU(N) Gibbs reflection form is proved equal to the
finite Wilson kernel-product/Bochner-Gram expression required by the OS theorem.
```

---

## Milestone 6 — boundary-fibered measure factorization

Status: **active frontier in PR #282**

The reflection-fixed time planes contain spatial links shared by the positive and negative halves. They cannot be duplicated into two independent Haar coordinates. The correct target is

```text
boundary configuration b
  -> conditional open-half measure mu_half(b)
  -> reflected form
       = integral_b integral_x integral_y
           <weightedFeature(b,x), weightedFeature(b,y)>
  -> integral_b ||integral_x weightedFeature(b,x)||^2
  -> nonnegativity.
```

Implemented:

- [~] involutive edge-orbit partition into positive, negative, and fixed boundary sectors;
- [~] boundary-fibered coordinate equivalence;
- [~] boundary-fibered index equivalence;
- [~] product-measure factorization scaffolding;
- [~] boundary Pi-measure construction;
- [~] boundary-fibered Bochner factorization interface;
- [~] boundary-fibered Bochner-Gram positivity theorem;
- [~] transfer to approximating and continuum reflection positivity.

Current validation state at head `592f3068bbb7f00b3a803ea75a3ed402d6674e3a`:

- [~] targeted boundary-fibered Pi-measure build step completed successfully;
- [ ] ordinary PR Lean Fast Check run 3844 must finish green;
- [ ] temporary diagnostic status propagation must be repaired or removed;
- [ ] temporary boundary-fibered workflow must be deleted before merge.

Still required mathematically:

- [ ] instantiate the boundary/positive/negative coordinate partition for the actual periodic lattice;
- [ ] prove the exact product Haar disintegration over fixed-plane boundary variables;
- [ ] include the Wilson action and crossing interaction in the fibered factorization;
- [ ] prove the actual pullback-form equality used by the boundary-fibered Gram certificate;
- [ ] verify integrability of the boundary moment norm square;
- [ ] close the concrete periodic `SU(N)` OS theorem.

Definition of done: no abstract boundary-fibered certificate remains uninstantiated in the final finite `SU(N)` reflection-positivity theorem.

---

## Milestone 7 — instantiate the physical weak-limit inputs

PR #282 supplies the constructor, but the decisive physical analytic objects remain open.

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

## Milestone 8 — nontrivial continuum theory and remaining OS axioms

- [ ] prove nontriviality and interacting character;
- [ ] prove uniqueness or characterize subsequence/phase selection;
- [ ] construct a separating gauge-invariant observable family;
- [ ] prove convergence of the required Schwinger distributions;
- [ ] prove Euclidean covariance;
- [ ] prove regularity;
- [ ] prove clustering;
- [ ] establish the remaining Osterwalder--Schrader axioms;
- [ ] align the probability-measure and observable-algebra formulations.

---

## Milestone 9 — continuum-relevant uniform gap mechanism

Single-link Dobrushin control may be too restrictive. Candidate routes are:

- [ ] block heat-bath dynamics or block Dobrushin estimates;
- [ ] approximate tensorization;
- [ ] multiscale/polymer estimates;
- [ ] reflection-positive transfer estimates;
- [ ] renormalization-group coercivity;
- [ ] another explicit scale-uniform mechanism.

Every route must track lattice spacing, physical volume, coupling, gauge group, and boundary conditions; distinguish heat-bath time from physical Euclidean time; and avoid assuming the desired gap.

---

## Milestone 10 — OS reconstruction and physical mass gap

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
- [ ] ordinary workflow green with no temporary diagnostics;
- [ ] new aggregate imports are in replay coverage;
- [ ] documentation claims have theorem/file anchors;
- [ ] placeholder inventory is current;
- [ ] stale or overtaken PRs are closed, rebased, or marked.

### Mathematical gate for PR #282 merge

- [ ] finite compact `SU(N)` law and gauge invariance replayed;
- [ ] weak-limit and observable/state spine replayed;
- [ ] exact Wilson RKHS feature and norm layer replayed;
- [ ] bounded-integrability/amplitude constructor replayed;
- [ ] boundary-fibered factorization either concretely completed or clearly left as an explicit conditional interface;
- [ ] no temporary workflow or claim overreach.

### Mathematical gate for a continuum existence claim

- [ ] concrete carrier, interpolation, and renormalized scaling;
- [ ] concrete coercive compactness estimate;
- [ ] concrete periodic `SU(N)` OS certificate;
- [ ] nontrivial interacting continuum law;
- [ ] remaining OS axioms.

### Mathematical gate for a physical mass-gap claim

- [ ] full OS reconstruction;
- [ ] continuum-relevant uniform gap estimate;
- [ ] physical Hamiltonian normalization;
- [ ] positive spectral lower bound with nonzero observable weight.

### External-claim gate

- [ ] independent replay and dependency audit;
- [ ] mathematical-physics specialist review;
- [ ] no circular use of the target gap or numerical value;
- [ ] public wording matches the theorem boundary.

## Execution order

```text
finish PR #282 boundary-fibered validation
  -> remove temporary diagnostics and obtain ordinary green CI
  -> finish exact periodic SU(N) boundary/Haar/action factorization
  -> merge the stable finite-law, weak-limit, observable, RKHS and OS layers
  -> choose the physical carrier and interpolation
  -> justify the renormalized coupling trajectory
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
