# MGAP4D Roadmap

This roadmap records the active proof-development path of the canonical Lean repository `itakura-hidetoshi/4d-mass-gap`.

## Status snapshot — 2026-06-24

The repository has two relevant development levels.

```text
main
  -> concrete finite Wilson heat-bath and exact Dobrushin route
     through merged PR #274

physical-4d-yang-mills-measure-limit
  -> active PR #282
  -> common-carrier weak limits
  -> finite and weak-limit OS positivity
  -> gauge-invariant OS Hilbert completion
  -> strongly continuous physical semigroup
  -> closed nonnegative right Hamiltonian
  -> finite-time Laplace resolvent and positive-shift surjectivity
  -> periodic translation invariance
  -> concrete integer temporal translations
```

The newest code milestone reviewed for this roadmap is:

```text
458c51b2a653229da24d605906abd48b833b6a75
```

At the time of this update, no workflow run was attached to that newest milestone. A dedicated periodic-translation run had succeeded on the preceding translation implementation, but the ordinary changed-Lean run on that predecessor was cancelled before completion. No final branch-wide ordinary-CI green claim is made here.

The repository does **not** yet contain an unconditional, physically complete construction of four-dimensional Yang--Mills theory with a positive mass gap.

## Governing distinctions

Every roadmap item must be read as one of the following.

1. **Concrete finite theorem:** proved from actual finite Wilson geometry and Gibbs laws.
2. **Theorem-generated transfer:** proved from explicit typed bridge data.
3. **Analytic OS construction:** constructed from reflection positivity, continuity, and covariance data.
4. **Physical continuum conclusion:** requires a justified carrier, scaling, regularity, nontriviality, and independent review.
5. **Internal normalization carrier:** transports a selected value but does not derive it physically.

New work should discharge a genuine dependency. Additional wrappers or readiness receipts are not priorities unless they close a concrete mathematical boundary.

## Completed finite Wilson layers

### A. Finite Gibbs probability and gauge geometry

Status: **proved**

- [x] finite periodic oriented Wilson geometry;
- [x] signed edge traversal and plaquette holonomy;
- [x] normalized product Haar measure;
- [x] normalized finite Wilson Gibbs probability law;
- [x] gauge covariance of signed steps and holonomy;
- [x] gauge invariance of action, Boltzmann weight, Haar law, and Gibbs law;
- [x] exact plaquette cardinality and normalized-action bounds.

### B. Heat-bath, Hilbert, and exact Dobrushin layer

Status: **proved on `main` through PR #274**

- [x] exact single-link conditional laws;
- [x] conditional-expectation projection `P_e`;
- [x] fluctuation projection `Q_e = I - P_e`;
- [x] detailed balance and Gibbs symmetry;
- [x] orthogonality and weighted Pythagoras;
- [x] finite Gibbs Hilbert equivalence;
- [x] canonical heat-bath Hamiltonian `H_HB = sum_e Q_e`;
- [x] exact identity `H_HB = |E| (I - P_scan)`;
- [x] centered random-scan Rayleigh contraction from the Dobrushin package;
- [x] active/shared-plaquette localization of Wilson influence;
- [x] finite-volume Poincare and Hamiltonian-gap consequences;
- [x] family finite-gap packages in the stated Dobrushin regime;
- [x] transfer-orbit contraction packages driven by the finite gap.

The former milestone “derive Dobrushin total variation to centered `L²` contraction” is closed. The remaining problem is the relation between finite heat-bath dynamics and the continuum physical OS Hamiltonian.

### C. Periodic and integer temporal translations

Status: **concrete finite theorems implemented; newest dedicated check pending at this snapshot**

- [x] periodic vertex translation equivalence;
- [x] periodic edge and plaquette translation equivalences;
- [x] configuration reindexing measurable equivalence;
- [x] covariance of signed boundary steps;
- [x] covariance of plaquette holonomy;
- [x] invariance of the periodic `SU(N)` Wilson action;
- [x] invariance of product normalized Haar measure;
- [x] invariance of the finite Wilson Gibbs probability law;
- [x] distinguished temporal displacement by each integer `k`;
- [x] zero law for integer temporal displacement;
- [x] addition law for integer temporal displacement;
- [x] negation law for integer temporal displacement;
- [x] measurable integer temporal configuration translation;
- [x] finite Gibbs invariance under integer temporal translations.

Principal files:

```text
MGAP4D/MathlibAnalytic/PeriodicHypercubicTranslationInvariance.lean
MGAP4D/MathlibAnalytic/PeriodicHypercubicIntegerTemporalTranslation.lean
```

## Active PR #282 weak-limit and OS layers

### D. Common-carrier weak-limit extraction

Status: **implemented from explicit hypotheses**

- [x] typed lattice embedding into one Polish physical carrier;
- [x] embedded probability measures;
- [x] action and observable pointwise bounds;
- [x] proper/coercive functional interfaces;
- [x] compact containment;
- [x] tightness;
- [x] Prokhorov subsequence;
- [x] weak convergence to a continuum probability measure;
- [x] continuous gauge-action transfer;
- [x] invariant event probabilities and observable laws;
- [x] bounded continuous expectation convergence;
- [x] two-point, connected-correlation, and finite n-point routes;
- [x] fixed real algebra of gauge-invariant bounded continuous observables;
- [ ] construct the physically intended distributional carrier;
- [ ] construct explicit interpolation or blocking;
- [ ] justify the renormalized coupling and scaling trajectory;
- [ ] prove the required coercive estimate for that physical construction;
- [ ] prove nontriviality and regularity of the limiting law.

### E. Finite and weak-limit reflection positivity

Status: **finite theorem proved; weak-limit theorem proved for bridged bounded observables**

- [x] even-periodic time reflection on vertices, links, and configurations;
- [x] positive, negative, and fixed-boundary sector classification;
- [x] boundary-fibered coordinate equivalence;
- [x] product Haar factorization;
- [x] orientation-corrected open-half integration;
- [x] temporal and spatial crossing-plaquette decomposition;
- [x] Wilson Gibbs density factorization;
- [x] RKHS/Gram construction for local crossing factors;
- [x] bounded-continuous finite-volume reflection positivity;
- [x] transfer of a fixed bounded continuous reflected quadratic observable through weak convergence;
- [ ] construct a sufficiently large continuum positive-time observable class;
- [ ] prove all pullback identifications for that class;
- [ ] prove the full intended continuum OS axiom package.

### F. Gauge-invariant OS Hilbert completion

Status: **implemented from supplied reflection-positive state data**

- [x] gauge-invariant expectation functional;
- [x] weak-star state interfaces;
- [x] positive-time observable subalgebra;
- [x] OS bilinear form;
- [x] null-space quotient;
- [x] real pre-Hilbert carrier;
- [x] Hilbert completion;
- [x] vacuum vector;
- [x] dense physical-state map.

### G. Positive-time semigroup and dense generator domain

Status: **implemented from observable translation and continuity data**

- [x] positive-time observable semigroup;
- [x] OS contraction estimate;
- [x] carrier contraction semigroup;
- [x] extension to the completed physical Hilbert space;
- [x] observable-state strong continuity interface;
- [x] full strong continuity on the completion;
- [x] right difference quotients;
- [x] right infinitesimal-generator domain;
- [x] right Hamiltonian `H = -G`;
- [x] Bochner time averages;
- [x] convergence of normalized time averages;
- [x] time averages lie in the generator domain;
- [x] density of the generator and Hamiltonian domains;
- [x] vacuum belongs to the domain and has zero Hamiltonian value.

### H. Closed Hamiltonian and finite-time Laplace resolvent

Status: **implemented in PR #282 source; final branch-wide ordinary CI still required**

- [x] nonnegative Hamiltonian quadratic form;
- [x] closability of the right Hamiltonian;
- [x] canonical `LinearPMap` graph closure;
- [x] uniqueness of graph limits;
- [x] nonnegativity of the closed Hamiltonian;
- [x] lower bound for `lambda I + Hbar`;
- [x] closed range of every positive shift;
- [x] finite-time Laplace integral;
- [x] generator-domain theorem for the Laplace integral;
- [x] resolvent identity with endpoint remainder;
- [x] vanishing endpoint remainder;
- [x] dense range of `lambda I + Hbar`;
- [x] surjectivity from dense plus closed range;
- [x] injectivity and bijectivity for `lambda > 0`;
- [x] maximal-accretive package;
- [ ] obtain final ordinary PR CI success on the terminal branch head;
- [ ] register the terminal aggregate module in the intended root import.

### I. Temporal-action constructor

Status: **generic constructor implemented; physical/discrete-to-continuous data remain open**

`periodicHypercubicSpecialUnitaryPhysicalTemporalAction` now constructs `PhysicalTemporalAction` from:

- [x] a real-parameter homeomorphism action on the physical carrier;
- [x] scale-dependent periodic lattice displacements;
- [x] interpolation equivariance;
- [x] automatic lattice-map measurability;
- [x] automatic finite Gibbs invariance generated from periodic translation invariance.

The constructor removes finite Gibbs invariance as an independent socket. It does **not** construct the physical real-parameter action, the scale-dependent displacement map, or interpolation equivariance.

Principal file:

```text
MGAP4D/MathlibAnalytic/PeriodicHypercubicSpecialUnitaryPhysicalTemporalAction.lean
```

### J. Semigroup symmetry and self-adjointness

Status: **theorem complete from a covariance bridge; concrete bridge construction remains open**

- [x] observable reflection/time-translation exchange implies carrier inner-product symmetry;
- [x] density extends symmetry to the completed semigroup;
- [x] semigroup symmetry implies formal symmetry of the generator and Hamiltonian;
- [x] graph closure preserves formal symmetry;
- [x] formal symmetry plus positive-shift surjectivity implies self-adjointness;
- [x] `WeakLimitTimeReflectionBridge` packages a sufficient continuum route;
- [x] self-adjointness theorem from that bridge and observable-state strong continuity;
- [ ] construct the continuum Euclidean-time action for the selected physical carrier;
- [ ] reconcile finite discrete time with real continuum time;
- [ ] prove interpolation equivariance for the selected embedding;
- [ ] construct the continuum configuration reflection;
- [ ] prove reflection conjugates forward translation to inverse translation;
- [ ] identify the abstract OS state with the continuum expectation state;
- [ ] discharge the positive-time restriction field;
- [ ] instantiate `WeakLimitTimeReflectionBridge`.

## Immediate milestone 1 — resolve the time-parameter boundary

The finite periodic lattice has a discrete temporal translation group. The continuum temporal-action interface is parameterized by `ℝ`.

A direct nontrivial group homomorphism from all real times to a finite periodic time group cannot simply be assumed. The formal route must make the approximation mechanism explicit.

Candidate rigorous routes are:

```text
A. discrete finite semigroups at each scale
   -> convergence to a strongly continuous continuum semigroup

B. lattice-step times a_n * k
   -> scale-dependent dense time sets
   -> extension by strong continuity

C. a revised temporal-action interface separating finite discrete time
   from continuum real time
```

Tasks:

- [ ] select the precise finite-time parameter type;
- [ ] define the scale-dependent conversion between lattice steps and physical Euclidean time;
- [ ] prove the finite group/semigroup laws on the correct parameter domain;
- [ ] avoid a floor/rounding map that falsely preserves addition for all real times;
- [ ] prove convergence or compatibility on a dense physical-time subset;
- [ ] extend to real time by continuity when justified;
- [ ] document the physical time normalization and units.

Definition of done:

```text
Finite integer temporal translations feed the continuum real-time Euclidean
semigroup through a theorem, not through an assumed real-to-integer group map.
```

## Immediate milestone 2 — instantiate the physical temporal action

Tasks:

- [ ] construct the real-parameter physical homeomorphism action on the chosen carrier;
- [ ] provide the scale-dependent lattice displacement on the correct time domain;
- [ ] prove interpolation equivariance;
- [ ] prove gauge commutation;
- [ ] derive invariance of every embedded law;
- [ ] pass invariance to the continuum weak limit;
- [ ] instantiate `PhysicalFourDimensionalYangMillsEuclideanTimeTranslationLimit`.

Definition of done:

```text
The selected Wilson approximation family produces a concrete continuum
Euclidean-time translation limit rather than assuming one as bridge data.
```

## Immediate milestone 3 — close the OS symmetry bridge

Tasks:

- [ ] construct the continuum configuration reflection homeomorphism;
- [ ] prove gauge commutation;
- [ ] identify observable reflection with precomposition by configuration reflection;
- [ ] prove `Theta tau_t = tau_{-t} Theta`;
- [ ] prove positive-time restriction agrees with observable semigroup translation;
- [ ] identify `omega` with the continuum weak-star expectation state;
- [ ] prove observable-state strong continuity for the instantiated system;
- [ ] instantiate `WeakLimitTimeReflectionBridge`;
- [ ] derive self-adjointness of the concrete graph-closed Hamiltonian.

Definition of done:

```text
The selected continuum weak-limit construction yields a concrete
self-adjoint nonnegative OS Hamiltonian through theorem application.
```

## Milestone 4 — derive a physical spectral gap

The current Hamiltonian route proves nonnegativity and conditional self-adjointness. It does not prove a positive spectral gap.

- [ ] prove vacuum uniqueness or characterize the zero-energy subspace;
- [ ] identify the vacuum-orthogonal closed subspace;
- [ ] connect finite heat-bath coercivity to the physical Euclidean semigroup;
- [ ] derive a lower bound uniform in lattice scale;
- [ ] prove continuum connected-correlation decay;
- [ ] convert decay to spectral support away from zero;
- [ ] exclude collapse to a trivial or degenerate continuum theory;
- [ ] track physical units without importing a target value.

Definition of done:

```text
The self-adjoint continuum OS Hamiltonian has a theorem-derived positive
spectral gap on the vacuum-orthogonal sector.
```

## Milestone 5 — physical continuum construction

- [ ] select the final distributional gauge-field carrier;
- [ ] define explicit interpolation, blocking, or renormalization maps;
- [ ] justify the coupling trajectory;
- [ ] prove tightness and regularity in the selected topology;
- [ ] establish Euclidean covariance, reflection positivity, and clustering;
- [ ] prove nontriviality and interacting character;
- [ ] identify the continuum observable algebra;
- [ ] prove compatibility of gauge reduction with the OS construction;
- [ ] obtain fresh-clone replay and independent mathematical review.

## Milestone 6 — real-time reconstruction

- [ ] complexify the real OS Hilbert space canonically;
- [ ] apply the spectral theorem to the concrete self-adjoint Hamiltonian;
- [ ] construct the real-time unitary group;
- [ ] reconstruct translations and the vacuum representation;
- [ ] verify the required Wightman properties;
- [ ] identify the physical particle/mass interpretation of the spectral gap.

The current Yin--Yang two-component file is an algebraic realification and Schrödinger-sign bridge only. It does not construct unitary real-time dynamics.

## Exact `33/20` lane

Status: **internal normalization/audit carrier only**

- [x] the value `33/20` is defined in an internal normalized package;
- [x] downstream spectral/PVM/R6/R7 interfaces transport that value;
- [x] documentation separates this carrier from the physical derivation;
- [ ] derive the physical OS Hamiltonian independently of the carrier;
- [ ] prove its positive spectral gap independently;
- [ ] derive any numerical value from the physical theory and normalization;
- [ ] prove equality with `33/20`, rather than preloading it;
- [ ] obtain independent expert review of any exact-value claim.

Until those items are closed, `33/20` must not be described as the proved physical four-dimensional Yang--Mills mass gap.

## Release gates

### Gate A — source correctness

- [ ] terminal PR #282 ordinary CI success;
- [ ] full fresh-clone `lake build`;
- [ ] `bash scripts/check.sh` success;
- [ ] terminal aggregate imports include every claimed theorem surface;
- [ ] placeholder and witness inventories are current;
- [ ] temporary diagnostic workflows are removed;
- [ ] obsolete or superseded pull requests are clearly marked.

### Gate B — concrete OS Hamiltonian

- [ ] rigorous discrete-to-continuous temporal bridge;
- [ ] instantiated continuum temporal action;
- [ ] instantiated continuum reflection;
- [ ] instantiated weak-limit time/reflection bridge;
- [ ] unconditional self-adjointness for the selected construction;
- [ ] vacuum uniqueness;
- [ ] positive vacuum-orthogonal spectral gap.

### Gate C — physical continuum theory

- [ ] physically justified carrier and scaling;
- [ ] regular, nontrivial continuum measure;
- [ ] Euclidean covariance and the required OS axioms;
- [ ] real-time reconstruction;
- [ ] physical normalization and units;
- [ ] no target value imported into the derivation.

### Gate D — external claim

- [ ] independent replay;
- [ ] theorem dependency review;
- [ ] external expert review;
- [ ] stable tagged release;
- [ ] archive metadata synchronized after the reviewed tag.

## Current priority order

1. Resolve the finite integer-time versus continuum real-time parameter boundary.
2. Prove interpolation equivariance and instantiate the physical temporal action.
3. Instantiate the weak-limit reflection/time-translation bridge and obtain the concrete self-adjoint OS Hamiltonian.
4. Complete branch-wide CI and aggregate-import registration.
5. Relate the finite heat-bath/Dobrushin gap to the physical OS semigroup and prove a uniform continuum spectral gap.
6. Construct and validate the physically intended continuum Yang--Mills theory.
7. Reassess any exact `33/20` claim only after the physical derivation is independent of the normalization carrier.
