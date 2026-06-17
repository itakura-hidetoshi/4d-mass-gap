# MGAP4D Roadmap

This roadmap records the active proof-development path of the canonical Lean repository `itakura-hidetoshi/4d-mass-gap`.

## Status snapshot — 2026-06-17

Current `main` contains a concrete finite Wilson heat-bath probability, orthogonal-projection, Gibbs-Hilbert, canonical Hamiltonian, random-scan scaling, and family-wide centered-Rayleigh implication lane. It also contains conditional bridges to transfer contraction, continuum clustering, and OS/Wightman reconstruction.

It does **not** yet contain an unconditional construction of four-dimensional Yang--Mills theory with a physical mass gap.

Latest merged checkpoint:

```text
PR #262
lift centered random-scan Rayleigh certificates to a finite Wilson family
and derive family-wide Poincare, Hamiltonian coercivity, and excitation bounds
```

Active open continuation:

```text
PR #263
construct an explicitly Dobrushin-rescaled finite heat-bath Hamiltonian
from the existing centered-Rayleigh certificate and normalized carrier scale
not yet on main
```

The active route is now:

```text
exact finite Wilson conditional laws
  -> P_e conditional-expectation projection
  -> Q_e = I - P_e fluctuation projection
  -> detailed balance and reversible product sums
  -> Gibbs symmetry, orthogonality, and Pythagoras
  -> weighted fluctuation-norm identity
  -> concrete Gibbs Hilbert equivalence
  -> canonical H_HB = sum_e Q_e
  -> H_HB = |E| (I - P_scan)
  -> centered random-scan Rayleigh coercivity
  -> family-wide finite Hamiltonian gap consequences
  -> Dobrushin influence theorem and scale-uniform Wilson bound
  -> physically normalized transfer Hamiltonian
  -> continuum clustering
  -> OS/Wightman reconstruction.
```

## Governing rule

New work should reduce a real proof obligation. Decorative receipt layers, duplicated readiness structures, or additional transport wrappers are not priorities unless they expose or discharge a concrete dependency.

The repository must distinguish:

1. finite identities proved from the actual Wilson Gibbs law;
2. conditional implication theorems whose hypotheses remain to be instantiated;
3. algebraic normalization and audit carriers;
4. physical continuum claims requiring independent construction and review.

---

## Completed finite Wilson layers

### A. Exact finite Gibbs probability layer

Status: **implemented on `main`**

- [x] finite Wilson action and normalized Gibbs PMF;
- [x] real Gibbs expectation and variance;
- [x] exact single-link conditional PMFs, expectations, and variances;
- [x] Gibbs-averaged local variance;
- [x] global single-link heat-bath Dirichlet form.

### B. Conditional-expectation and orthogonal-projection layer

Status: **implemented on `main`**

- [x] off-link agreement and fiber invariance;
- [x] idempotent single-link projection `P_e`;
- [x] real-linear endomorphism form and range/fixed-point characterization;
- [x] complementary projection `Q_e = I - P_e`;
- [x] decomposition, mutual annihilation, and idempotence;
- [x] exact detailed balance and reversible product-sum identity;
- [x] Gibbs-pairing symmetry of `P_e` and `Q_e`;
- [x] Gibbs orthogonality of the projection and fluctuation ranges;
- [x] Gibbs-weighted Pythagorean decomposition;
- [x] exact local identity
  `E_mu[Var_e(f)] = <Q_e f, Q_e f>_mu`;
- [x] full Dirichlet form as the sum of local Gibbs squared norms.

Representative merged PRs: #218--#242, #246, #249, and #250.

### C. Concrete finite Gibbs Hilbert layer

Status: **implemented on `main`**

- [x] finite Euclidean Gibbs Hilbert carrier;
- [x] observable embedding `f(A) -> sqrt(mu(A)) f(A)`;
- [x] Euclidean inner product equals the Gibbs pairing;
- [x] normalized vacuum `sqrt(mu)`;
- [x] vacuum expectation equals Gibbs expectation;
- [x] centered Hilbert norm equals Gibbs variance;
- [x] strict positivity of every finite Gibbs probability;
- [x] inverse observation map `x(A) / sqrt(mu(A))`;
- [x] embedding/observation linear equivalence.

Representative merged PRs: #251 and #252.

### D. Canonical finite heat-bath Hamiltonian layer

Status: **implemented on `main`**

- [x] observable generator `H_HB = sum_e Q_e`;
- [x] Gibbs symmetry of the generator;
- [x] transport through the Gibbs Hilbert equivalence;
- [x] Hilbert-space symmetry;
- [x] zero vacuum energy;
- [x] exact quadratic-form identity with the heat-bath Dirichlet form;
- [x] canonical finite Hamiltonian bridge from heat-bath Poincare coercivity;
- [x] vacuum-centered and vacuum-orthogonal coercivity consequences.

Representative merged PRs: #253, #254, and #260.

### E. Random-scan and family-wide Rayleigh layer

Status: **finite algebra and conditional family implication implemented**

- [x] concrete normalized random-scan sweep;
- [x] exact identity `H_HB = |E| (I - P_scan)`;
- [x] exact Dirichlet/Rayleigh-defect identity;
- [x] Gibbs centering has zero mean;
- [x] centering preserves local fluctuations and Dirichlet energy;
- [x] centered Rayleigh contraction certificate for one system;
- [x] correctly scaled coercivity `|E|(1-rho)`;
- [x] centered Rayleigh contraction implies finite heat-bath Poincare coercivity;
- [x] composition with the canonical finite Hamiltonian lower bound;
- [x] family-wide centered-Rayleigh certificate package;
- [x] family-wide Poincare, vacuum-orthogonal coercivity, and excitation-eigenvalue consequences.

Representative merged PRs: #256--#258, #260, and #262.

### F. Dobrushin normalization layer

Status: **scale separation implemented; analytic conversion remains open**

- [x] finite Dobrushin matrix and row-sum interfaces;
- [x] heat-bath gap `lambda_HB = 1 - alpha`;
- [x] normalized random-scan rate
  `rho = 1 - (1-alpha)/|E|`;
- [x] Markov-range proof `0 <= rho < 1` for nonempty edge sets;
- [x] normalization identity `|E|(1-rho) = 1-alpha`;
- [x] proof that the former unscaled exact-gap certificates are uninhabited;
- [x] explicit positive normalized-carrier scale and algebraic multiplication identity;
- [x] separate certificate for centered Gibbs `L²`/Rayleigh contraction;
- [ ] derive that centered Rayleigh contraction from the Dobrushin influence assumptions;
- [ ] construct actual Wilson influence coefficients;
- [ ] prove a volume- and lattice-spacing-uniform row-sum or block bound.

Representative merged PRs: #255, #256, #258, and #261.

---

## Immediate milestone 1 — evaluate the explicitly rescaled Dobrushin Hamiltonian lane

PR #263 proposes:

```text
Dobrushin centered-Rayleigh certificate
  -> (1-alpha) heat-bath Poincare coercivity
  -> multiplication by scale_HB
  -> rescaled finite Hamiltonian quadratic form
  -> exactGapValueReal lower bound on the vacuum-orthogonal sector.
```

Tasks:

- [ ] verify all Lean statements and imports in PR #263;
- [ ] retain explicit dependence on
  `FiniteLatticeWilsonDobrushinRandomScanRayleighCertificate`;
- [ ] state clearly that the rescaling is algebraic, not dynamically derived;
- [ ] avoid calling the rescaled operator the physical transfer Hamiltonian;
- [ ] add the file to review anchors only after merge;
- [ ] decide whether this lane clarifies the dependency graph or merely repackages the normalized carrier.

Definition of done:

```text
The rescaled finite Hamiltonian lane is mathematically correct, dependency-
transparent, and cannot be misread as deriving the physical scale or 33/20
from Wilson dynamics.
```

---

## Immediate milestone 2 — derive Dobrushin data to centered `L²` contraction

Goal: replace the remaining certificate socket by a genuine theorem.

The current Dobrushin matrix controls conditional laws in total variation. The canonical Hamiltonian lane requires a centered Gibbs-pairing Rayleigh estimate. These are not definitionally identical.

Tasks:

- [ ] define the local oscillation or martingale-difference seminorm controlled by one-link changes;
- [ ] prove conditional expectation contracts the selected local quantities;
- [ ] derive the Dobrushin matrix action on the local vector of oscillations;
- [ ] prove the required row-sum, operator-norm, or approximate-tensorization estimate;
- [ ] convert it rigorously to
  `<P_scan f,f>_mu <= rho <f,f>_mu` for centered `f`;
- [ ] preserve the exact factor `|E|` between normalized scan and generator;
- [ ] lift the theorem through the family package merged in PR #262;
- [ ] provide finite-system compile smokes and small explicit examples.

Definition of done:

```text
FiniteLatticeWilsonDobrushinMatrixData is consumed by a theorem that produces
the centered random-scan Rayleigh certificate required by the canonical
heat-bath Hamiltonian lane.
```

---

## Milestone 3 — prove a scale-uniform Wilson influence estimate

Goal: discharge the principal finite-volume analytic input for the non-Abelian Wilson measures.

- [ ] derive explicit conditional-law sensitivity bounds from the Wilson action;
- [ ] quantify coupling, plaquette incidence, gauge group, lattice spacing, and boundary dependence;
- [ ] prove a row-sum or block-Dobrushin bound in a stated parameter regime;
- [ ] determine whether single-link dynamics is sufficient or block dynamics is required;
- [ ] prove constants uniform in the selected continuum approximation family;
- [ ] avoid assuming the desired mass gap inside the coefficient package.

This is a genuine hard analytic milestone. Adding a field that asserts the estimate does not close it.

---

## Milestone 4 — derive the physical normalization and transfer Hamiltonian

The finite canonical heat-bath Hamiltonian and family-wide conditional gap lane are constructed. The remaining issue is their physical scale and relation to the transfer Hamiltonian.

Completed formal separation:

```text
lambda_HB   = heat-bath coercivity constant
rho_scan    = normalized random-scan rate
Delta_norm  = scale_HB * lambda_HB.
```

The current explicit definition

```text
scale_HB = exactGapValueReal / lambda_HB
```

proves an algebraic equality but uses the pre-existing normalized carrier. It is not a dynamical derivation.

Open tasks:

- [ ] construct the finite transfer operator from the Wilson measure and time slicing;
- [ ] identify its physical Hilbert space, vacuum, and centered sector;
- [ ] prove positivity, symmetry/self-adjointness, and transfer normalization;
- [ ] derive the conversion between `H_HB` and the physical transfer Hamiltonian from dynamics;
- [ ] track lattice spacing, coupling, Euclidean time step, and physical units;
- [ ] prove the scale uniformly across the approximation family;
- [ ] ensure no target value is imported into the derivation.

Definition of done:

```text
The physical Hamiltonian lower bound follows from constructed transfer
operators and a dynamically proved scale relation, not from defining the scale
as exactGapValueReal divided by the heat-bath gap.
```

---

## Milestone 5 — transfer orbit and continuum clustering

- [ ] construct the correlation-orbit representation for the physical transfer operator;
- [ ] prove a scale-uniform readout/initial-state amplitude bound;
- [ ] prove finite-volume connected-correlation decay with the derived finite gap;
- [ ] prove convergence of observables and correlations;
- [ ] prove the limiting correlation is nontrivial;
- [ ] transfer the physically normalized decay rate to the continuum.

---

## Milestone 6 — continuum measure and OS/Wightman reconstruction

Existing projective-limit and OS/Wightman files provide typed routes and comparison theorems. They do not by themselves discharge all analytic hypotheses of the physical theory.

- [ ] prove tightness and regularity for the selected approximation family;
- [ ] prove reflection positivity and Euclidean invariance for the concrete limiting law;
- [ ] prove clustering using the physically normalized gap route;
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
- [x] the heat-bath and normalized layers are formally separated;
- [ ] derive the physical scale independently of `exactGapValueReal`;
- [ ] construct the continuum physical Yang--Mills Hamiltonian independently of that value;
- [ ] derive its spectral infimum and positive observable weight;
- [ ] prove, rather than preload, equality with `33/20`;
- [ ] obtain external review of any exact-value claim.

Until those open items are closed, documentation must describe `33/20` as an internal normalization/audit value, not as the solved physical mass gap.

---

## Release gates

### Gate A — source-level correctness

- [ ] full `lake build` from a fresh clone;
- [ ] `bash scripts/check.sh` passes;
- [x] the old contradictory unscaled random-scan structures are proved uninhabited;
- [ ] imports include every claimed current theorem surface;
- [ ] placeholder and witness inventory is current;
- [ ] obsolete open PRs are closed or clearly marked as superseded.

### Gate B — mathematical closure

- [ ] Dobrushin-to-centered-Rayleigh theorem proved;
- [ ] scale-uniform Wilson estimate proved;
- [ ] physical normalization/transfer bridge proved;
- [ ] nontrivial continuum limit proved;
- [ ] OS/Wightman reconstruction hypotheses discharged.

### Gate C — external claim

- [ ] independent replay;
- [ ] theorem dependency review;
- [ ] external expert review;
- [ ] stable tagged release;
- [ ] Zenodo/archive metadata synchronized only after the reviewed tag.

## Current priority order

1. Review PR #263 as an algebraic rescaling lane, not a physical derivation.
2. Prove the Dobrushin TV/influence to centered Gibbs `L²` Rayleigh theorem.
3. Prove a genuine scale-uniform Wilson influence or block-dynamics estimate.
4. Derive the physical transfer-time/generator normalization independently of `exactGapValueReal`.
5. Establish uniform transfer contraction and nontrivial continuum clustering.
6. Discharge the OS/Wightman hypotheses and obtain independent review.
7. Reassess any exact `33/20` claim only after the physical construction is independent of the normalization carrier.