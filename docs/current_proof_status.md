# Current proof status

**Updated:** 2026-06-24  
**Stable finite checkpoint:** merged PR #274  
**Active development:** PR #282, `physical-4d-yang-mills-measure-limit`  
**Reviewed code baseline:** `54b3404d5096ec007f757e1c288d472bc3ac8a3d`

## Repository and verification status

PR #282 is open, non-draft, and mergeable.

At the reviewed code baseline:

- `Temporary Periodic Translation Check` run 3 completed successfully;
- `PR Lean Fast Check` run 4274 was cancelled before the changed-Lean build completed;
- the current documentation therefore does not claim final ordinary-CI green status for the complete active branch.

The theorem bodies are the authoritative mathematical surface. Workflow status is recorded separately because a theorem may be present in source while the final branch-wide verification is still pending.

## Status summary

The active source tree now contains the following route:

```text
actual finite periodic SU(N) Wilson Gibbs laws
  -> finite gauge invariance
  -> finite periodic translation invariance
  -> exact Wilson conditional laws
  -> exact Dobrushin and finite heat-bath gap consequences
  -> common-carrier lattice embeddings
  -> tightness and Prokhorov weak limits
  -> continuum gauge-symmetry transfer
  -> finite even-periodic reflection positivity
  -> weak-limit nonnegativity for bridged bounded continuous OS observables
  -> gauge-invariant positive-time observable algebra
  -> OS pre-Hilbert quotient and Hilbert completion
  -> physical contraction semigroup
  -> strong continuity
  -> dense right-generator domain
  -> nonnegative closable right Hamiltonian
  -> graph-closed Hamiltonian
  -> finite-time Laplace resolvent
  -> positive-shift surjectivity and bijectivity
  -> self-adjointness from the concrete reflection/time-translation symmetry bridge.
```

The current hard boundary is no longer finite-volume Dobrushin contraction or positive-shift surjectivity. It is the construction of the model-specific continuum temporal/reflection covariance bridge and the derivation of a positive physical spectral gap.

## Proved on `main`

The finite Wilson lane through merged PR #274 contains:

- exact finite Wilson Gibbs probability laws;
- exact single-link conditional laws;
- `P_e` conditional-expectation projections;
- `Q_e = I - P_e` fluctuation projections;
- detailed balance and Gibbs symmetry;
- orthogonality and weighted Pythagoras;
- the concrete finite Gibbs Hilbert realization;
- the canonical heat-bath Hamiltonian
  `H_HB = sum_e Q_e`;
- the exact relation
  `H_HB = |E| (I - P_scan)`;
- canonical Dobrushin random-scan Rayleigh contraction;
- exact active/shared-plaquette Wilson influence localization;
- finite-volume and family Poincare/Hamiltonian-gap consequences;
- transfer-orbit contraction packages in the stated finite regime.

The previous documentation statement that

```text
Dobrushin TV row-sum bound
  -> centered Gibbs L2/Rayleigh contraction
```

was still open is obsolete.

## Implemented in active PR #282

### 1. Physical weak-limit route

The branch supplies typed structures and theorems for:

- finite oriented periodic Wilson systems;
- measurable lattice embeddings into one Polish carrier;
- embedded probability measures;
- normalized action and observable bounds;
- proper/coercive functional control;
- compact containment and tightness;
- Prokhorov subsequences;
- weak convergence to a continuum probability measure;
- transfer of continuous gauge symmetry;
- invariant event probabilities and observable laws;
- bounded continuous expectation convergence;
- two-point, connected-correlation, and finite n-point routes;
- the real algebra of gauge-invariant bounded continuous observables.

This route is conditional on the supplied physical carrier, interpolation, and coercive data. The repository has not yet selected and justified the final distributional continuum construction.

### 2. Finite even-periodic reflection positivity

The branch proves finite Wilson Gibbs reflection positivity using:

- exact even-periodic reflection geometry;
- boundary/open-half decomposition;
- boundary-fibered coordinate factorization;
- product Haar transport;
- temporal and spatial crossing-sector factorization;
- positive-semidefinite local Wilson kernels;
- finite tensor-product RKHS/Gram constructions;
- bounded-continuous reflected observables.

The terminal finite theorem is:

```lean
periodicHypercubicEvenWilsonGibbs_reflectionPositive_boundedContinuous
```

### 3. Weak-limit OS nonnegativity

For a fixed bounded continuous physical quadratic observable equipped with a concrete pullback bridge, finite reflection positivity passes to the continuum weak limit.

The principal theorem is:

```lean
physical_yang_mills_evenPeriodicWilsonOS_continuum_nonneg
```

This is not yet a theorem that every intended continuum positive-time observable has such a bridge.

### 4. Gauge-invariant OS Hilbert completion

From supplied reflection-positive gauge-invariant state data, the branch constructs:

- the positive-time observable subalgebra;
- the OS bilinear form;
- the null-space quotient;
- the real pre-Hilbert carrier;
- the Hilbert completion;
- the vacuum;
- a dense physical-state map.

### 5. Strongly continuous physical semigroup

From positive-time observable translation, contraction, and observable-state continuity, the branch constructs:

- a carrier contraction semigroup;
- its bounded extension to the Hilbert completion;
- strong continuity for every physical vector;
- the canonical right-generator domain;
- the right infinitesimal generator;
- the right Hamiltonian `H = -G`;
- Bochner time averages;
- density of the generator/Hamiltonian domain;
- the zero-energy vacuum relation.

### 6. Closed nonnegative Hamiltonian and resolvent

The branch source implements:

- nonnegativity of the right Hamiltonian form;
- closability;
- graph closure as a `LinearPMap`;
- uniqueness of graph limits;
- nonnegativity of the closed Hamiltonian;
- the lower bound for `lambda I + Hbar`;
- closed range of positive shifts;
- finite-time Laplace integrals;
- generator-domain membership of those integrals;
- the endpoint-corrected resolvent identity;
- vanishing of the endpoint remainder;
- density and then surjectivity of the shifted range;
- injectivity and bijectivity for `lambda > 0`;
- the maximal-accretive package.

The finite-time Laplace construction therefore removes positive-shift surjectivity as a separate analytic assumption.

### 7. Self-adjointness theorem

The branch proves:

```text
formal symmetry of Hbar
  + surjectivity of I + Hbar
  -> Hbar is self-adjoint.
```

It also proves:

```text
observable reflection/time-translation exchange
  -> symmetry of the completed Euclidean semigroup
  -> formal symmetry of the right generator
  -> formal symmetry of the right Hamiltonian
  -> formal symmetry of the graph closure
  -> self-adjointness.
```

The theorem

```lean
closedRightHamiltonian_isSelfAdjoint
```

is available from `WeakLimitTimeReflectionBridge` together with observable-state strong continuity.

The remaining issue is to instantiate that bridge from the actual selected continuum construction.

### 8. Finite periodic translation invariance

The newest finite theorem constructs periodic translations of:

- vertices;
- physical links;
- plaquettes;
- signed boundary incidences;
- configurations.

It proves:

- covariance of signed step values;
- covariance of plaquette holonomy;
- invariance of the Wilson action;
- invariance of the product Haar law;
- invariance of the finite periodic `SU(N)` Wilson Gibbs law.

The dedicated translation workflow succeeded on the reviewed code baseline.

The finite theorem does not by itself construct the real-parameter continuum Euclidean-time action. The interpolation-equivariance and continuum-limit connection remain open.

## Exact self-adjointness frontier

The current model-dependent bridge requires:

```text
continuum Euclidean-time homeomorphisms
+ finite/embedded-law invariance
+ interpolation equivariance
+ gauge commutation
+ continuum configuration reflection
+ reflection/time inversion
+ positive-time observable restriction
+ continuum-state identification
+ observable-state strong continuity.
```

Once those fields are instantiated, the source theorem produces a self-adjoint nonnegative graph-closed physical Hamiltonian.

## Spectral-gap frontier

No theorem currently proves that the constructed closed OS Hamiltonian has a strictly positive spectral gap.

Still required are:

- a concrete instantiated self-adjoint OS Hamiltonian for the selected continuum construction;
- characterization and preferably uniqueness of the vacuum;
- a vacuum-orthogonal invariant sector;
- a uniform relation between finite Wilson/heat-bath decay and the OS semigroup;
- continuum clustering or spectral-support control;
- a positive lower bound independent of lattice scale;
- physical normalization and units;
- nontriviality of the continuum theory.

## Exact `33/20` dependency

The source tree contains:

```lean
hamiltonianPVMSpectralNormalized3320Value := (33 : Real) / 20
```

and older interfaces transport that internal normalized value.

The active OS Hamiltonian route has not proved:

- that its spectral gap is positive;
- that its gap equals `33/20`;
- that `33/20` follows from Wilson dynamics, continuum scaling, or physical units.

Therefore `33/20` remains an internal normalization/audit value, not an independently derived physical mass gap.

## Claim table

| Claim | Status |
|---|---|
| Finite periodic `SU(N)` Wilson Gibbs law | constructed |
| Finite gauge invariance | proved |
| Finite periodic translation invariance | proved in PR #282 source; dedicated check succeeded |
| Exact Wilson Dobrushin to centered Rayleigh contraction | proved |
| Exact plaquette-supported influence profile | proved |
| Finite heat-bath Poincare/Hamiltonian gap | proved in the stated regime |
| Common-carrier weak-limit extraction | proved from explicit embedding/coercivity hypotheses |
| Continuum gauge invariance | proved from continuous action and interpolation-equivariance data |
| Finite even-periodic Wilson reflection positivity | proved |
| Weak-limit OS nonnegativity for a bridged bounded observable | proved |
| Full continuum OS reflection positivity | open |
| Gauge-invariant OS Hilbert completion | constructed from supplied data |
| Strongly continuous physical contraction semigroup | constructed from supplied continuity data |
| Dense right-Hamiltonian domain | implemented |
| Closed nonnegative right Hamiltonian | implemented |
| Positive-shift surjectivity | implemented by finite-time Laplace resolvent |
| Self-adjointness from semigroup symmetry | proved |
| Concrete weak-limit time/reflection bridge | open |
| Concrete self-adjoint continuum OS Hamiltonian | conditional on that bridge |
| Positive physical spectral gap | open |
| Vacuum uniqueness | open |
| Nontrivial physical continuum Yang--Mills theory | open |
| Independent physical derivation of `33/20` | open |
| Final ordinary CI green on the current PR branch | not yet claimed |
| External consensus | not claimed |

## Immediate next steps

1. Package the finite periodic translations as the lattice temporal action at every approximation scale.
2. Prove interpolation equivariance and construct the continuum Euclidean-time action.
3. Construct the continuum reflection and instantiate `WeakLimitTimeReflectionBridge`.
4. Obtain final ordinary CI success and register all terminal aggregate imports.
5. Derive vacuum uniqueness, continuum clustering, and a positive spectral gap for the constructed OS Hamiltonian.
6. Complete the physical continuum carrier, scaling, regularity, nontriviality, and external review.

Lean theorem bodies are authoritative. Conditional bridge structures, source files without final branch-wide CI, and internal exact-value carriers must not be presented as unconditional physical results.
