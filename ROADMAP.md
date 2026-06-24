# MGAP4D Roadmap

This roadmap records the active proof-development path of the canonical Lean repository `itakura-hidetoshi/4d-mass-gap`.

## Status snapshot — 2026-06-24

The repository now has two relevant development levels.

```text
main
  -> finite Wilson heat-bath and exact Dobrushin route through merged PR #274

physical-4d-yang-mills-measure-limit
  -> active PR #282
  -> physical weak limits, finite and weak-limit OS positivity,
     gauge-invariant OS Hilbert completion, strongly continuous semigroup,
     right Hamiltonian closure and Laplace resolvent,
     plus finite periodic translation invariance
```

PR #282 is open, non-draft, and mergeable.

The code baseline reviewed for this roadmap is:

```text
54b3404d5096ec007f757e1c288d472bc3ac8a3d
```

Verification at that baseline:

- dedicated `Temporary Periodic Translation Check` run 3: success;
- ordinary `PR Lean Fast Check` run 4274: cancelled before completion of the changed-Lean build;
- no final branch-wide ordinary-CI green claim is made here.

The repository does **not** yet contain an unconditional, physically complete construction of four-dimensional Yang--Mills theory with a positive mass gap.

## Governing distinctions

Every roadmap item must be classified as one of the following.

1. **Concrete finite theorem:** proved from the actual finite Wilson geometry and Gibbs law.
2. **Theorem-generated transfer:** proved from an explicit typed bridge whose fields remain to be constructed physically.
3. **Analytic OS construction:** constructed from reflection-positive state, continuity, and covariance data.
4. **Physical continuum conclusion:** requires justified carrier, scaling, regularity, nontriviality, and independent review.
5. **Internal normalization carrier:** transports a selected value but does not independently derive it.

New work should discharge a real dependency. Additional receipt layers, duplicated wrappers, or renamed readiness structures are not priorities unless they close a concrete mathematical boundary.

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
- [x] centered random-scan Rayleigh contraction from the canonical Dobrushin package;
- [x] active/shared-plaquette localization of Wilson influence;
- [x] finite-volume Poincare and Hamiltonian-gap consequences;
- [x] family finite-gap packages in the stated Dobrushin regime;
- [x] transfer-orbit contraction packages driven by the finite gap.

The old roadmap item “derive Dobrushin TV to centered `L²` contraction” is closed. The remaining issue is no longer the finite Dobrushin conversion. It is the relation between the finite heat-bath dynamics and the continuum physical OS Hamiltonian.

### C. Finite periodic translation invariance

Status: **proved in PR #282 source; dedicated workflow succeeded**

- [x] periodic vertex translation equivalence;
- [x] periodic edge and plaquette translation equivalences;
- [x] configuration reindexing measurable equivalence;
- [x] covariance of signed boundary steps;
- [x] covariance of plaquette holonomy;
- [x] invariance of the canonical periodic `SU(N)` Wilson action;
- [x] invariance of product normalized Haar measure;
- [x] invariance of the finite Wilson Gibbs probability law;
- [ ] select and package the temporal subgroup at every approximation scale;
- [ ] connect it to the physical interpolation map;
- [ ] derive the continuum temporal-action structure.

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
- [x] two-point, connected-correlation, and finite n-point observable routes;
- [x] fixed real algebra of gauge-invariant bounded continuous observables;
- [ ] construct the physically intended distributional carrier;
- [ ] construct explicit interpolation or blocking;
- [ ] justify the renormalized coupling/scaling trajectory;
- [ ] prove the required proper coercive estimate for that physical construction;
- [ ] prove nontriviality and regularity of the limiting law.

### E. Finite even-periodic Wilson reflection positivity

Status: **proved**

- [x] even-periodic time reflection on vertices, links, and configurations;
- [x] positive, negative, and fixed boundary-sector classification;
- [x] boundary-fibered coordinate equivalence;
- [x] product Haar factorization;
- [x] orientation-corrected open-half integration;
- [x] temporal and spatial crossing-plaquette decomposition;
- [x] Wilson Gibbs density factorization;
- [x] RKHS/Gram kernel construction for local crossing factors;
- [x] bounded-continuous finite-volume reflection positivity;
- [x] transfer of a fixed bounded continuous reflected quadratic observable through weak convergence;
- [ ] construct a sufficiently large continuum positive-time observable class with all required pullback identifications;
- [ ] prove the full intended continuum OS axiom package for that class.

### F. Gauge-invariant OS Hilbert completion

Status: **implemented from supplied reflection-positive state data**

- [x] gauge-invariant expectation functional;
- [x] weak-star state interfaces;
- [x] positive-time observable subalgebra;
- [x] OS bilinear form;
- [x] null-space quotient;
- [x] pre-Hilbert structure;
- [x] Hilbert completion;
- [x] vacuum vector;
- [x] dense physical-state linear map.

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
- [x] time-average convergence;
- [x] time averages lie in the generator domain;
- [x] density of the right-generator and right-Hamiltonian domains;
- [x] vacuum belongs to the domain and has zero Hamiltonian value.

### H. Closed nonnegative Hamiltonian and finite-time Laplace resolvent

Status: **implemented in PR #282 source; final ordinary branch CI still required**

- [x] nonnegative Hamiltonian quadratic form;
- [x] closability of the right Hamiltonian;
- [x] canonical `LinearPMap` graph closure;
- [x] uniqueness of graph limits;
- [x] nonnegativity of the closed Hamiltonian;
- [x] lower bound for `lambda I + Hbar`;
- [x] closed range of every positive shift;
- [x] finite-time Laplace integral
  `R_{lambda,h} psi = integral_0^h exp(-lambda s) T_s psi ds`;
- [x] generator-domain theorem for the Laplace integral;
- [x] resolvent identity with endpoint remainder;
- [x] endpoint remainder tends to zero;
- [x] dense range of `lambda I + Hbar`;
- [x] surjectivity from dense plus closed range;
- [x] injectivity and bijectivity of positive shifts;
- [x] maximal-accretive package;
- [ ] obtain final ordinary PR CI success on the complete terminal head;
- [ ] ensure the terminal aggregate module is registered in the intended root import.

### I. Semigroup symmetry and self-adjointness

Status: **theorem complete from a concrete covariance bridge; bridge construction remains open**

- [x] observable reflection/time-translation exchange implies carrier inner-product symmetry;
- [x] density extends symmetry to the completed semigroup;
- [x] semigroup symmetry implies formal symmetry of the generator and Hamiltonian;
- [x] graph closure preserves formal symmetry;
- [x] formal symmetry plus positive-shift surjectivity implies self-adjointness;
- [x] `WeakLimitTimeReflectionBridge` packages a sufficient continuum route;
- [x] self-adjointness theorem from that bridge and observable-state strong continuity;
- [ ] construct the continuum Euclidean-time action from the concrete periodic translations;
- [ ] prove interpolation equivariance for the chosen physical embedding;
- [ ] construct the continuum configuration reflection;
- [ ] prove reflection conjugates forward translation to inverse translation;
- [ ] identify the abstract OS state with the continuum expectation state;
- [ ] discharge the positive-time restriction field;
- [ ] instantiate `WeakLimitTimeReflectionBridge` for the actual selected continuum construction.

## Immediate milestone 1 — concrete temporal action through the weak limit

Goal: turn the new finite translation theorem into the actual continuum temporal-action structure used by the OS Hamiltonian lane.

Tasks:

- [ ] choose the finite temporal displacement corresponding to each approximation-scale Euclidean time;
- [ ] package the lattice maps as the `latticeTranslate` field of `PhysicalTemporalAction`;
- [ ] reuse the proved finite Gibbs invariance;
- [ ] prove measurability of every lattice temporal map;
- [ ] prove interpolation equivariance;
- [ ] construct the physical homeomorphism group on the common carrier;
- [ ] prove its group law and gauge commutation;
- [ ] derive invariance of every embedded law;
- [ ] pass invariance to the continuum weak limit.

Definition of done:

```text
The chosen periodic Wilson approximation family produces an instantiated
PhysicalFourDimensionalYangMillsEuclideanTimeTranslationLimit, rather than
assuming one as external bridge data.
```

## Immediate milestone 2 — close the OS symmetry bridge

Goal: instantiate the exact hypothesis that turns the closed nonnegative Hamiltonian into a self-adjoint operator.

Tasks:

- [ ] construct the continuum configuration reflection homeomorphism;
- [ ] prove gauge commutation;
- [ ] identify observable reflection with precomposition by configuration reflection;
- [ ] prove `Theta tau_t = tau_{-t} Theta`;
- [ ] prove that positive-time restriction agrees with the observable semigroup translation;
- [ ] identify `omega` with the continuum weak-star expectation state;
- [ ] prove observable-state strong continuity for the instantiated system;
- [ ] instantiate `WeakLimitTimeReflectionBridge`;
- [ ] derive self-adjointness of the graph-closed physical Hamiltonian without an unfilled covariance socket.

Definition of done:

```text
The selected continuum weak-limit construction yields a concrete
self-adjoint nonnegative OS Hamiltonian through theorem application.
```

## Milestone 3 — derive a physical spectral gap

The current right-Hamiltonian route constructs nonnegativity and, conditionally, self-adjointness. It does not prove a positive spectral gap.

Tasks:

- [ ] prove vacuum uniqueness or characterize the zero-energy subspace;
- [ ] identify the vacuum-orthogonal closed subspace;
- [ ] transfer finite-volume decay or coercivity to the OS semigroup;
- [ ] connect the finite heat-bath gap to the physical Euclidean-time semigroup;
- [ ] derive a uniform positive lower bound independent of lattice scale;
- [ ] prove continuum connected-correlation decay;
- [ ] convert decay to spectral support away from zero;
- [ ] exclude collapse to a trivial or degenerate continuum theory;
- [ ] track physical units and normalization without importing a target value.

Definition of done:

```text
The self-adjoint continuum OS Hamiltonian has a theorem-derived positive
spectral gap on the vacuum-orthogonal sector.
```

## Milestone 4 — physical continuum construction

Tasks:

- [ ] select the final distributional gauge-field carrier;
- [ ] define explicit interpolation, blocking, or renormalization maps;
- [ ] justify the coupling trajectory;
- [ ] prove tightness and regularity in the selected topology;
- [ ] establish Euclidean covariance, reflection positivity, and clustering;
- [ ] prove nontriviality and interacting character;
- [ ] identify the continuum observable algebra;
- [ ] prove compatibility of gauge reduction with the OS construction;
- [ ] obtain fresh-clone replay and independent mathematical review.

## Milestone 5 — real-time reconstruction

Tasks:

- [ ] complexify the real OS Hilbert space in a canonical way;
- [ ] apply the spectral theorem to the concrete self-adjoint Hamiltonian;
- [ ] construct the real-time unitary group;
- [ ] reconstruct translations and the vacuum representation;
- [ ] verify the required Wightman properties;
- [ ] identify the physical particle/mass interpretation of the spectral gap.

The current Yin--Yang two-component file is an algebraic realification and Schrödinger-sign bridge only. It does not yet construct unitary real-time dynamics.

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
- [ ] obsolete or superseded pull requests are clearly closed or marked.

### Gate B — concrete OS Hamiltonian

- [ ] instantiated continuum temporal action;
- [ ] instantiated continuum reflection;
- [ ] instantiated weak-limit time/reflection bridge;
- [ ] unconditional self-adjointness for the selected construction;
- [ ] vacuum uniqueness;
- [ ] positive vacuum-orthogonal spectral gap.

### Gate C — physical continuum theory

- [ ] physically justified carrier and scaling;
- [ ] regular, nontrivial continuum measure;
- [ ] Euclidean covariance and full required OS axioms;
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

1. Connect the concrete periodic translation theorem to `PhysicalTemporalAction` and the physical interpolation.
2. Instantiate the weak-limit reflection/time-translation bridge and obtain the concrete self-adjoint OS Hamiltonian.
3. Complete branch-wide CI and aggregate-import registration.
4. Relate the finite heat-bath/Dobrushin gap to the physical OS semigroup and prove a uniform continuum spectral gap.
5. Construct and validate the physically intended continuum Yang--Mills theory.
6. Reassess any exact `33/20` claim only after the physical derivation is independent of the normalization carrier.
