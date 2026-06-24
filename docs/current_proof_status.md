# Current proof status

**Updated:** 2026-06-24  
**Stable finite checkpoint:** merged PR #274  
**Active development:** PR #282, `physical-4d-yang-mills-measure-limit`  
**Newest reviewed code milestone:** `458c51b2a653229da24d605906abd48b833b6a75`

## Repository and verification status

PR #282 is open and non-draft.

At the time of this update:

- the newest milestone adds the dedicated check target for concrete integer temporal translations;
- no workflow run was yet attached to that newest commit;
- the preceding periodic-translation implementation had passed its dedicated workflow;
- the ordinary changed-Lean run on that predecessor was cancelled before completion;
- final ordinary-CI green status for the complete active branch is not claimed.

Theorem bodies are the authoritative mathematical surface. Source status and workflow status are recorded separately.

## Status summary

```text
actual finite periodic SU(N) Wilson Gibbs laws
  -> finite gauge invariance
  -> arbitrary periodic translation invariance
  -> concrete integer temporal translations
  -> exact Wilson conditional laws
  -> exact Dobrushin and finite heat-bath gap consequences
  -> common-carrier lattice embeddings
  -> tightness and Prokhorov weak limits
  -> continuum gauge-symmetry transfer
  -> finite even-periodic reflection positivity
  -> weak-limit nonnegativity for bridged bounded OS observables
  -> gauge-invariant positive-time observable algebra
  -> OS pre-Hilbert quotient and Hilbert completion
  -> physical contraction semigroup
  -> strong continuity
  -> dense right-generator domain
  -> nonnegative closable right Hamiltonian
  -> graph-closed Hamiltonian
  -> finite-time Laplace resolvent
  -> positive-shift surjectivity and bijectivity
  -> self-adjointness from reflection/time-translation symmetry.
```

The hard boundary is no longer finite-volume Dobrushin contraction, finite Gibbs translation invariance, or positive-shift surjectivity. It is now the rigorous passage from discrete finite-lattice time to real continuum Euclidean time, the construction of the continuum reflection/covariance bridge, and the derivation of a positive physical spectral gap.

## Proved on `main`

The finite Wilson lane through merged PR #274 contains:

- exact finite Wilson Gibbs probability laws;
- exact single-link conditional laws;
- `P_e` conditional-expectation projections;
- `Q_e = I - P_e` fluctuation projections;
- detailed balance and Gibbs symmetry;
- orthogonality and weighted Pythagoras;
- the concrete finite Gibbs Hilbert realization;
- the canonical heat-bath Hamiltonian `H_HB = sum_e Q_e`;
- the exact relation `H_HB = |E| (I - P_scan)`;
- canonical Dobrushin random-scan Rayleigh contraction;
- exact active/shared-plaquette Wilson influence localization;
- finite-volume and family Poincare/Hamiltonian-gap consequences;
- transfer-orbit contraction packages in the stated finite regime.

The previous documentation statement

```text
Dobrushin TV row-sum bound
  -> centered Gibbs L2/Rayleigh contraction
```

as an open problem is obsolete.

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

This route is conditional on the supplied physical carrier, interpolation, and coercive data. The final distributional continuum construction has not yet been selected and justified.

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

```lean
physical_yang_mills_evenPeriodicWilsonOS_continuum_nonneg
```

This does not yet prove that every intended continuum positive-time observable has the required bridge.

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
- density of the generator and Hamiltonian domains;
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

The finite-time Laplace construction removes positive-shift surjectivity as a separate assumption.

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

`WeakLimitTimeReflectionBridge` packages sufficient continuum covariance data. Together with observable-state strong continuity, it yields the theorem `closedRightHamiltonian_isSelfAdjoint`.

The remaining task is to instantiate that bridge for the selected physical continuum construction.

### 8. Arbitrary periodic translation invariance

The branch constructs periodic translations of vertices, physical links, plaquettes, signed boundary incidences, and configurations.

It proves:

- covariance of signed step values;
- covariance of plaquette holonomy;
- invariance of the Wilson action;
- invariance of the product Haar law;
- invariance of the finite periodic `SU(N)` Wilson Gibbs law.

### 9. Concrete integer temporal translations

The distinguished temporal coordinate is now selected explicitly.

For every `k : ℤ`, the branch defines:

```lean
periodicHypercubicIntegerTemporalDisplacement n k
periodicHypercubicIntegerTemporalConfigurationTranslation n k
```

and proves:

- the temporal coordinate equals `k` modulo the period;
- spatial coordinates remain zero;
- zero, addition, and negation laws;
- measurable configuration translation;
- invariance of the finite periodic `SU(N)` Wilson Gibbs law.

The principal finite invariance theorem is:

```lean
periodicHypercubicSpecialUnitary_gibbs_map_integerTemporalTranslation_eq_self
```

### 10. Physical temporal-action constructor

The branch contains:

```lean
periodicHypercubicSpecialUnitaryPhysicalTemporalAction
```

This constructs the abstract `PhysicalTemporalAction` from:

- a real-parameter homeomorphism action on the physical carrier;
- scale-dependent periodic lattice displacements;
- interpolation equivariance.

Measurability and finite Gibbs invariance are generated automatically from the periodic translation theorem. They are no longer independent assumptions.

The constructor does not supply the physical action, the real-time-to-lattice displacement relation, or interpolation equivariance.

## Exact temporal frontier

The finite lattice time group is discrete and periodic. The continuum action is parameterized by `ℝ`.

The missing theorem must not assume that a rounding or floor map from real time to integer lattice steps preserves addition for all real times.

A rigorous route must instead use one of the following patterns or an equivalent construction:

```text
discrete finite semigroups
  -> convergence to a continuum strongly continuous semigroup

lattice times a_n * k on scale-dependent dense subsets
  -> compatibility and convergence
  -> extension by strong continuity

or

a revised interface separating finite discrete time from continuum real time.
```

After this parameter boundary is resolved, the remaining fields are:

- physical continuum time-translation homeomorphisms;
- scale-dependent lattice displacement data;
- interpolation equivariance;
- gauge commutation;
- continuum reflection;
- reflection/time inversion;
- positive-time observable restriction;
- continuum-state identification;
- observable-state strong continuity.

## Spectral-gap frontier

No theorem currently proves that the constructed closed OS Hamiltonian has a strictly positive spectral gap.

Still required are:

- an instantiated self-adjoint OS Hamiltonian for the selected continuum construction;
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

Older interfaces transport that internal normalized value.

The active OS Hamiltonian route has not proved that its spectral gap is positive, that it equals `33/20`, or that `33/20` follows from Wilson dynamics, continuum scaling, or physical units.

Therefore `33/20` remains an internal normalization/audit value, not an independently derived physical mass gap.

## Claim table

| Claim | Status |
|---|---|
| Finite periodic `SU(N)` Wilson Gibbs law | constructed |
| Finite gauge invariance | proved |
| Arbitrary periodic translation invariance | proved |
| Integer temporal displacement group laws | proved in source |
| Finite Gibbs invariance under integer temporal translation | proved in source |
| Newest integer-temporal dedicated check | pending at this snapshot |
| Generic physical temporal-action constructor | implemented from supplied physical action and equivariance data |
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
| Discrete finite-time to real continuum-time bridge | open |
| Concrete weak-limit time/reflection bridge | open |
| Concrete self-adjoint continuum OS Hamiltonian | conditional on those bridges |
| Positive physical spectral gap | open |
| Vacuum uniqueness | open |
| Nontrivial physical continuum Yang--Mills theory | open |
| Independent physical derivation of `33/20` | open |
| Final ordinary CI green on the current branch | not claimed |
| External consensus | not claimed |

## Immediate next steps

1. Resolve the finite integer-time versus continuum real-time parameter boundary.
2. Prove interpolation equivariance and instantiate the physical temporal action.
3. Construct continuum reflection and instantiate `WeakLimitTimeReflectionBridge`.
4. Obtain final ordinary CI success and register terminal aggregate imports.
5. Derive vacuum uniqueness, continuum clustering, and a positive spectral gap for the constructed OS Hamiltonian.
6. Complete the physical continuum carrier, scaling, regularity, nontriviality, and external review.

Lean theorem bodies are authoritative. Conditional bridge structures, source files without final branch-wide CI, and internal exact-value carriers must not be presented as unconditional physical results.
