# MGAP4D Roadmap

This roadmap records the active proof-development path of the canonical Lean repository `itakura-hidetoshi/4d-mass-gap`.

## Status snapshot — 2026-06-17

Current `main` contains a substantial finite Wilson heat-bath construction and a collection of conditional bridges to Hamiltonian gaps, transfer contraction, continuum clustering, and OS/Wightman reconstruction.

It does **not** yet contain an unconditional construction of four-dimensional Yang--Mills theory with a physical mass gap.

Latest merged checkpoint:

```text
PR #241
finite_lattice_singleLinkHeatBath_reversible_product_sum
```

Current open continuation:

```text
PR #242
Gibbs-pairing symmetry of the single-link heat-bath projection
not yet on main
```

The active route is now:

```text
exact finite Wilson conditional laws
  -> P_e conditional-expectation projection
  -> Q_e = I - P_e fluctuation projection
  -> detailed balance and reversible product sums
  -> Gibbs self-adjointness and orthogonality
  -> quantitative heat-bath coercivity
  -> correctly normalized Hamiltonian gap
  -> transfer contraction
  -> continuum clustering
  -> OS/Wightman reconstruction
```

## Governing rule

New work should reduce a real proof obligation. Decorative receipt layers, duplicated readiness structures, or additional transport wrappers are not priorities unless they expose or discharge a concrete dependency.

The repository must distinguish:

1. finite identities proved from the actual Wilson Gibbs law;
2. conditional implication theorems whose hypotheses remain to be instantiated;
3. internal normalization/audit carriers;
4. physical continuum claims requiring independent construction and review.

---

## Completed finite Wilson layers

### A. Exact finite Gibbs probability layer

Status: **implemented on `main`**

- [x] finite Wilson action and normalized Gibbs PMF;
- [x] real Gibbs expectation;
- [x] Gibbs variance and nonnegativity;
- [x] exact single-link conditional Boltzmann weights and PMFs;
- [x] conditional expectation and conditional variance;
- [x] Gibbs-averaged local variance;
- [x] global single-link heat-bath Dirichlet form.

Representative merged PRs: #208--#212.

### B. Conditional-expectation projection layer

Status: **implemented algebraically; weighted symmetry is the next step**

- [x] off-link agreement and fiber invariance;
- [x] `OffLinkFiberConstant` observables;
- [x] idempotent single-link projection `P_e`;
- [x] fixed-point and range characterization;
- [x] real-linear endomorphism form;
- [x] complementary projection `Q_e = I - P_e`;
- [x] decomposition `f = P_e f + Q_e f`;
- [x] mutual annihilation and idempotence;
- [x] kernel/range characterizations;
- [x] local conditional variance as the second moment of `Q_e f`;
- [x] global Dirichlet form as total fluctuation energy.

Representative merged PRs: #218, #219, #224--#226.

### C. Reversibility layer

Status: **finite detailed balance and product-sum reversibility implemented**

- [x] exact pointwise detailed balance in `ENNReal`;
- [x] real-valued detailed-balance identity;
- [x] involutive configuration--gauge update exchange;
- [x] pointwise forward/backward transition transport;
- [x] finite-sum invariance under equivalence;
- [x] reversible full product-sum identity.

Representative merged PRs: #227, #230, #232, #233, #235, #236, #239--#241.

Not yet merged:

- [ ] Gibbs-pairing symmetry of `P_e` — PR #242.

### D. Random-scan and Dobrushin interfaces

Status: **operators and data interfaces implemented; decisive estimates absent**

- [x] exact one-link heat-bath operator;
- [x] concrete random-scan average over links;
- [x] conditional total-variation distance;
- [x] finite-system Dobrushin matrix interface;
- [x] zero diagonal and row-sum fields;
- [x] approximation-family uniform Dobrushin interface;
- [ ] derive random-scan variance contraction from the Dobrushin matrix assumptions;
- [ ] construct actual Wilson influence coefficients;
- [ ] prove a volume- and lattice-spacing-independent row-sum bound.

Representative merged PRs: #220--#223.

---

## Immediate milestone 1 — close the local Hilbert projection package

Goal: turn the exact finite conditional expectation into an orthogonal projection for the Gibbs-weighted real Hilbert structure.

- [ ] merge or reproduce the valid part of PR #242 on current `main`;
- [ ] prove
  `⟨P_e f, g⟩_μ = ⟨f, P_e g⟩_μ`;
- [ ] prove Gibbs-weighted orthogonality
  `⟨P_e f, Q_e g⟩_μ = 0`;
- [ ] prove the Pythagorean decomposition;
- [ ] prove
  `E_μ[Var_e(f)] = ||Q_e f||²_{L²(μ)}`;
- [ ] package `P_e` as a self-adjoint idempotent operator in the finite weighted Hilbert space;
- [ ] package `Q_e` as the orthogonal complementary projection.

Definition of done:

```text
The local heat-bath energy is represented by the squared norm of an explicitly
self-adjoint complementary projection, without an unproved measure-theoretic
or finite-sum reindexing step.
```

---

## Immediate milestone 2 — repair the gap normalization

Status: **blocking issue**

The current random-scan contraction structures require

```text
0 <= rho < 1
exactGapValueReal <= 1 - rho.
```

But the current carrier satisfies

```text
1 < exactGapValueReal
```

and hence no such data can exist, because `0 <= rho` gives `1 - rho <= 1`.

The roadmap must not treat this interface as an instantiable route to the normalized value `33/20` until the scale mismatch is repaired.

Choose and formalize one of the following mathematically coherent designs:

### Preferred design: separate gaps

```text
lambda_HB       := heat-bath / Markov coercivity constant
Delta_norm      := normalized physical Hamiltonian gap
scale_HB > 0    := transfer-time or generator normalization
Delta_norm = scale_HB * lambda_HB
lambda_HB <= 1 - rho
```

Tasks:

- [ ] introduce a distinct heat-bath gap carrier;
- [ ] remove `exactGapValueReal <= 1 - rho` from raw random-scan data;
- [ ] add an explicit scale-conversion structure;
- [ ] prove that the old random-scan exact-gap structure is uninhabited under `exactGapValueReal_above_one`;
- [ ] migrate downstream Poincare/Hamiltonian bridges to the new scaled formulation.

Alternative design:

- [ ] use a continuous-time generator such as `Σ_e (I - P_e)` with an explicitly declared time normalization;
- [ ] prove its relation to the random-scan average and to the transfer Hamiltonian.

Definition of done:

```text
No theorem requires a normalized Markov contraction coefficient bounded by one
to be numerically equal to a physical normalized gap known to be above one.
```

---

## Milestone 3 — Dobrushin data to operator contraction

Goal: derive a genuine theorem, rather than a data socket, connecting influence coefficients to contraction of the concrete random-scan operator.

- [ ] define the local oscillation/seminorm controlled by one-link changes;
- [ ] prove conditional expectation contracts the appropriate local oscillations;
- [ ] derive the Dobrushin matrix action on oscillation vectors;
- [ ] prove a row-sum or operator-norm contraction estimate;
- [ ] convert that estimate to variance contraction or approximate tensorization;
- [ ] state the exact dependence on the number of links and scan normalization;
- [ ] provide finite-system compile-smoke and small explicit examples.

Definition of done:

```text
A concrete theorem consumes FiniteLatticeWilsonDobrushinMatrixData and produces
a correctly normalized coercivity or contraction estimate for the actual
random-scan heat-bath operator.
```

---

## Milestone 4 — prove the scale-uniform Wilson estimate

Goal: discharge the principal finite-volume analytic input for the non-Abelian Wilson measures.

- [ ] derive explicit conditional-law sensitivity bounds from the Wilson action;
- [ ] quantify the dependence on coupling, plaquette incidence, gauge group, lattice spacing, and boundary conditions;
- [ ] prove a row-sum or block-Dobrushin bound in a stated parameter regime;
- [ ] determine whether single-link Dobrushin is sufficient or whether block dynamics is required;
- [ ] prove constants uniform in the selected continuum approximation family;
- [ ] avoid assuming the desired mass gap inside the coefficient package.

This is a genuine hard analytic milestone. Merely adding fields that assert the estimate does not close it.

---

## Milestone 5 — physical Hamiltonian and quadratic-form identification

Current conditional bridge:

```text
heat-bath Poincare input
  + Hilbert realization
  + variance/norm identity
  + Dirichlet/Hamiltonian quadratic-form identity
  -> vacuum-sector Hamiltonian lower bound
```

Open tasks:

- [ ] construct the finite transfer Hilbert space from the Wilson measure;
- [ ] identify the vacuum vector and centered subspace;
- [ ] construct the transfer operator and its Hamiltonian normalization;
- [ ] prove self-adjointness/positivity in the relevant finite theory;
- [ ] prove the observable realization is sufficiently rich;
- [ ] prove the exact quadratic-form identity with the correctly scaled heat-bath generator;
- [ ] track physical units and transfer-time normalization explicitly.

Definition of done:

```text
The Hamiltonian lower bound follows from constructed operators and proved
identities, not from fields named `...Ready` or from a preloaded exact-gap value.
```

---

## Milestone 6 — transfer orbit and continuum clustering

The repository already contains conditional propagation theorems. The remaining work is to instantiate their analytic hypotheses.

- [ ] construct the correlation-orbit representation;
- [ ] prove a scale-uniform readout/initial-state amplitude bound;
- [ ] prove finite-volume connected-correlation decay with the derived finite gap;
- [ ] prove convergence of the observables and correlations;
- [ ] prove the limiting correlation is nontrivial;
- [ ] transfer the correctly normalized decay rate to the continuum.

---

## Milestone 7 — continuum measure and OS/Wightman reconstruction

Existing projective-limit and OS/Wightman files provide typed routes and comparison theorems. They do not by themselves supply all analytic hypotheses of the physical theory.

- [ ] prove tightness/regularity for the selected approximation family;
- [ ] prove reflection positivity and Euclidean invariance for the concrete limiting law;
- [ ] prove clustering using the repaired gap route;
- [ ] prove nontriviality and required regularity;
- [ ] reconstruct the physical Hilbert space, vacuum, translations, and Hamiltonian;
- [ ] identify the physical spectral gap without importing the target value;
- [ ] obtain independent mathematical review and fresh-clone replay receipts.

---

## Exact `33/20` lane

Status: **internal normalized audit carrier; not an independently derived physical value**

- [x] `hamiltonianPVMSpectralNormalized3320Value` is defined as `33/20`;
- [x] an internal package transports that value through spectral/PVM-shaped interfaces;
- [x] `exactGapValueReal` projects the package value;
- [x] downstream R6/R7 and terminal audit surfaces carry the same equality;
- [ ] construct a physical Yang--Mills Hamiltonian independently of that value;
- [ ] derive its spectral infimum and positive observable weight;
- [ ] prove, rather than preload, equality with `33/20`;
- [ ] obtain external review of the claimed exact value.

Until those open items are closed, documentation must describe `33/20` as an internal normalization/audit value, not as the solved physical mass gap.

---

## Release gates

### Gate A — source-level correctness

- [ ] full `lake build` from a fresh clone;
- [ ] `bash scripts/check.sh` passes;
- [ ] no active contradiction or uninhabitable data structure is presented as an available construction;
- [ ] imports include all claimed current theorem surfaces;
- [ ] placeholder and witness inventory is current.

### Gate B — mathematical closure

- [ ] uniform finite-volume estimate proved;
- [ ] normalization bridge proved;
- [ ] physical Hamiltonian constructed;
- [ ] nontrivial continuum limit proved;
- [ ] OS/Wightman reconstruction hypotheses discharged.

### Gate C — external claim

- [ ] independent replay;
- [ ] theorem dependency review;
- [ ] external expert review;
- [ ] stable tagged release;
- [ ] Zenodo/archive metadata synchronized only after the reviewed tag.

## Current priority order

1. Finish Gibbs-pairing symmetry and projection orthogonality.
2. Repair the random-scan/physical-gap scale mismatch.
3. Derive Dobrushin-to-contraction theorems.
4. Prove a genuine scale-uniform Wilson estimate.
5. Construct and identify the physical transfer Hamiltonian.
6. Establish nontrivial continuum clustering and OS/Wightman reconstruction.
7. Reassess any exact `33/20` claim only after the physical construction is independent of the normalization carrier.
