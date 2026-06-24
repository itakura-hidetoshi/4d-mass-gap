# MGAP4D

**MGAP4D** is Hidetoshi Itakura's canonical Lean 4 / Mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory and the mass-gap problem.

```text
Canonical repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

## Current status — 2026-06-24

The repository is an active formal-development and review surface. It is **not** a completed or externally validated solution of the four-dimensional Yang--Mills existence and mass-gap problem.

Two development levels must be distinguished.

```text
main
  -> concrete finite Wilson heat-bath and exact Dobrushin route
     through merged PR #274

physical-4d-yang-mills-measure-limit
  -> active PR #282
  -> common-carrier weak limits, finite and weak-limit OS positivity,
     gauge-invariant OS Hilbert completion, strongly continuous semigroups,
     closed right Hamiltonians, finite-time Laplace resolvents,
     periodic translation invariance, and integer temporal translations
```

The newest code milestone reviewed for this document is:

```text
458c51b2a653229da24d605906abd48b833b6a75
```

At the time of this update, no workflow run was yet attached to that newest milestone. A dedicated periodic-translation workflow had succeeded on its predecessor, while the ordinary changed-Lean run on that predecessor was cancelled before completion. This README therefore makes no final ordinary-CI green claim for the complete current branch.

## Current concrete proof spine

```text
finite periodic SU(N) Wilson geometry and Haar--Gibbs laws
  -> exact gauge invariance
  -> exact periodic translation invariance
  -> concrete integer temporal translations
  -> exact Wilson conditional laws and Dobrushin control
  -> finite heat-bath Poincare and Hamiltonian-gap consequences
  -> physical lattice embeddings into a common Polish carrier
  -> tightness and Prokhorov subsequential weak limits
  -> continuum gauge-symmetry transfer
  -> finite even-periodic Wilson reflection positivity
  -> weak-limit nonnegativity for bridged OS observables
  -> gauge-invariant positive-time observable algebra
  -> OS pre-Hilbert quotient and Hilbert completion
  -> positive-time contraction semigroup
  -> strong continuity on the completed physical Hilbert space
  -> dense right-generator domain
  -> closable nonnegative right Hamiltonian
  -> graph-closed Hamiltonian
  -> finite-time Laplace resolvent
  -> positive-shift surjectivity and bijectivity
  -> self-adjointness from reflection/time-translation symmetry.
```

The arrows above have different logical statuses. Finite-volume statements are concrete theorems. Weak-limit and OS conclusions are theorem-generated from explicit bridge structures. The final physical continuum carrier, scaling, covariance bridge, nontriviality, and spectral gap remain open.

## 1. Finite Wilson and exact Dobrushin lane

The finite Wilson lane starts from actual finite-volume Wilson Gibbs laws and exact one-link conditional distributions.

It includes:

- finite Wilson action and normalized Gibbs probability laws;
- exact single-link conditional laws;
- conditional-expectation projections `P_e`;
- fluctuation projections `Q_e = I - P_e`;
- detailed balance, Gibbs symmetry, orthogonality, and weighted Pythagoras;
- the concrete finite Gibbs Hilbert realization;
- the canonical heat-bath Hamiltonian `H_HB = sum_e Q_e`;
- the exact identity `H_HB = |E| (I - P_scan)`;
- canonical Dobrushin random-scan Rayleigh contraction;
- exact active/shared-plaquette localization of Wilson influence;
- finite-volume and family finite-gap consequences in the stated Dobrushin regime;
- transfer-orbit contraction packages generated from those finite gaps.

The former documentation statement that the Dobrushin total-variation to centered-`L²` conversion was open is obsolete. That finite analytic route was completed before PR #282, through merged PR #274.

This finite heat-bath Hamiltonian has not yet been identified with the continuum physical OS Hamiltonian.

## 2. Physical weak-limit and gauge-symmetry lane

PR #282 constructs typed routes from actual finite periodic `SU(N)` Wilson Gibbs laws to subsequential probability measures on one supplied Polish physical carrier.

The branch contains:

- signed oriented periodic Wilson geometry;
- normalized Haar--Gibbs probability measures;
- exact finite gauge invariance;
- exact plaquette cardinality and normalized-action bounds;
- measurable lattice embeddings and interpolation interfaces;
- proper/coercive functional interfaces;
- compact containment and tightness;
- Prokhorov subsequences;
- weak convergence to a `PhysicalFourDimensionalYangMillsWeakLimit`;
- transfer of continuous gauge actions to the limiting law;
- invariant event probabilities and observable laws;
- convergence and invariance of bounded continuous expectations;
- two-point, connected-correlation, and finite n-point routes;
- the real algebra of gauge-invariant bounded continuous observables.

The weak-limit constructor is explicit but physically conditional. A final distributional carrier, concrete blocking or interpolation, renormalized coupling trajectory, and coercive estimate appropriate to physical four-dimensional Yang--Mills theory remain to be supplied.

## 3. Reflection positivity

The even-periodic Wilson lane derives finite-volume Osterwalder--Schrader positivity from boundary-fibered coordinates, product Haar factorization, temporal-sector decomposition, and Gram/RKHS kernels.

The terminal bounded-continuous finite theorem is:

```lean
periodicHypercubicEvenWilsonGibbs_reflectionPositive_boundedContinuous
```

For a fixed bounded continuous physical quadratic observable equipped with a concrete pullback bridge, finite nonnegativity passes through weak convergence to the continuum measure:

```lean
physical_yang_mills_evenPeriodicWilsonOS_continuum_nonneg
```

This does not yet construct the full continuum positive-time observable class required for a complete OS reconstruction.

## 4. Gauge-invariant OS Hilbert and Hamiltonian lane

From supplied gauge-invariant reflection-positive state data, positive-time translations, and continuity data, the branch constructs:

```text
positive-time observable algebra
  -> OS bilinear form
  -> null-space quotient
  -> real pre-Hilbert carrier
  -> Hilbert completion
  -> dense physical-state map and vacuum
  -> positive-time contraction semigroup
  -> observable-state strong continuity
  -> strongly continuous physical contraction semigroup
  -> right infinitesimal generator
  -> right Hamiltonian H = -G
  -> dense domain from Bochner time averages
  -> nonnegative quadratic form
  -> closability and graph closure Hbar
  -> lower bound and closed range for lambda I + Hbar
  -> finite-time Laplace resolvent identity
  -> surjectivity and bijectivity for every lambda > 0
  -> maximal-accretive package.
```

The finite-time Laplace resolvent removes positive-shift surjectivity as an independent hypothesis.

The branch then proves:

```text
formal symmetry of Hbar
  -> self-adjointness of Hbar.
```

Formal symmetry follows from symmetry of the completed Euclidean semigroup, which follows from the observable reflection/time-translation exchange identity. The remaining model-dependent work is to instantiate that covariance bridge for the selected continuum construction.

## 5. Periodic and temporal translations

The branch now contains three related layers.

### Periodic displacement invariance

For every periodic lattice displacement, it constructs vertex, edge, plaquette, signed-boundary, and configuration translations and proves:

- covariance of signed step values;
- covariance of plaquette holonomy;
- invariance of the Wilson action;
- invariance of product normalized Haar measure;
- invariance of the finite periodic `SU(N)` Wilson Gibbs law.

### Integer temporal subgroup

The distinguished temporal coordinate is now selected explicitly. For every integer `k`, the branch constructs the displacement by `k` temporal lattice units and proves:

- zero, addition, and negation laws for the displacement;
- the corresponding measurable configuration translation;
- invariance of the finite Wilson Gibbs law under that integer temporal translation.

The principal file is:

```text
MGAP4D/MathlibAnalytic/PeriodicHypercubicIntegerTemporalTranslation.lean
```

### Physical temporal-action constructor

`periodicHypercubicSpecialUnitaryPhysicalTemporalAction` constructs the abstract `PhysicalTemporalAction` from:

- a real-parameter homeomorphism action on the physical carrier;
- scale-dependent periodic lattice displacements;
- interpolation equivariance.

Finite-volume Gibbs invariance and measurability are generated automatically from the periodic translation theorem rather than assumed as separate fields.

The remaining temporal frontier is therefore precise:

```text
integer/discrete finite-lattice time translations
  -> a justified lattice-spacing-dependent time parametrization
  -> interpolation equivariance
  -> real-parameter continuum Euclidean-time action
  -> continuum measure invariance
  -> reflection/time inversion
  -> observable semigroup symmetry
  -> concrete self-adjoint OS Hamiltonian.
```

A nontrivial choice is required here. The finite periodic time group is discrete, whereas the current continuum temporal-action interface is parameterized by `ℝ`. The formal development must either construct a rigorous discrete-to-continuous limiting bridge or refine the interface so that no unjustified real-to-integer group identification is assumed.

## What the repository currently establishes

| Surface | Current reading |
|---|---|
| Finite periodic `SU(N)` Wilson Gibbs law | Concrete |
| Finite gauge invariance | Proved |
| Arbitrary periodic translation invariance | Proved |
| Integer temporal translation and Gibbs invariance | Proved in source; newest dedicated check pending at this snapshot |
| Generic physical temporal-action constructor | Implemented from physical action and interpolation-equivariance data |
| Exact Wilson Dobrushin locality and centered Rayleigh contraction | Proved before PR #282 |
| Finite heat-bath Hamiltonian gap in the stated regime | Proved |
| Common-carrier weak-limit extraction | Constructed from explicit embedding/coercivity hypotheses |
| Continuum gauge invariance | Proved from continuous action and interpolation-equivariance data |
| Finite even-periodic reflection positivity | Proved |
| Weak-limit OS nonnegativity for a bridged observable | Proved |
| Gauge-invariant OS Hilbert completion | Constructed from supplied reflection-positive state data |
| Strongly continuous physical contraction semigroup | Constructed from supplied continuity data |
| Dense, closable, nonnegative right Hamiltonian | Implemented |
| Positive-shift surjectivity of the closed Hamiltonian | Implemented by the finite-time Laplace route |
| Self-adjointness theorem | Proved from the OS covariance/symmetry bridge |
| Instantiated continuum temporal/reflection bridge | Open |
| Positive spectral gap of the constructed OS Hamiltonian | Open |
| Vacuum uniqueness and nontriviality | Open |
| Physical continuum Yang--Mills construction | Open |
| Physical derivation of `33/20` | Not established |
| Final ordinary CI green on the current branch | Not claimed |
| External mathematical consensus | Not claimed |

## Exact `33/20` boundary

The source tree contains an internal normalized value `33/20` carried through older spectral, PVM, R6, and R7 interfaces.

That lane is an internal normalization and dependency-audit surface. It is not an independent derivation of the physical four-dimensional Yang--Mills mass gap.

The active OS Hamiltonian lane has not proved that its spectral gap is positive, that it equals `33/20`, or that the physical normalization yields `33/20`.

Read `docs/exact_gap_layer_separation.md` for the dependency-level separation.

## Primary review anchors

| Topic | File |
|---|---|
| Concise status | `docs/current_proof_status.md` |
| Development plan | `ROADMAP.md` |
| Physical measure frontier | `docs/physical_yang_mills_measure_frontier.md` |
| Gauge-symmetry observable spine | `docs/physical_yang_mills_symmetry_observable_spine.md` |
| Periodic translation invariance | `MGAP4D/MathlibAnalytic/PeriodicHypercubicTranslationInvariance.lean` |
| Integer temporal translations | `MGAP4D/MathlibAnalytic/PeriodicHypercubicIntegerTemporalTranslation.lean` |
| Physical temporal-action constructor | `MGAP4D/MathlibAnalytic/PeriodicHypercubicSpecialUnitaryPhysicalTemporalAction.lean` |
| Finite bounded-continuous reflection positivity | `MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenWilsonGibbsBoundedContinuousReflectionPositivity.lean` |
| Weak-limit OS nonnegativity | `MGAP4D/MathlibAnalytic/PhysicalYangMillsEvenPeriodicWilsonOSWeakLimit.lean` |
| Gauge-invariant OS Hilbert completion | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSHilbertCompletion.lean` |
| Strong continuity | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSPositiveTimeObservableStrongContinuity.lean` |
| Right Hamiltonian | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSRightHamiltonian.lean` |
| Laplace resolvent and surjectivity | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSClosedRightHamiltonianSurjective.lean` |
| Self-adjointness theorem | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSClosedRightHamiltonianSelfAdjoint.lean` |
| Semigroup symmetry bridge | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSSemigroupSymmetry.lean` |
| Weak-limit time/reflection bridge | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSWeakLimitTimeReflection.lean` |
| Aggregate OS Hamiltonian route | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSHamiltonianSpine.lean` |

## Replay

Pinned toolchain:

```text
Lean:    leanprover/lean4:v4.30.0-rc2
mathlib: v4.30.0-rc2
```

```bash
git clone https://github.com/itakura-hidetoshi/4d-mass-gap.git
cd 4d-mass-gap
git checkout physical-4d-yang-mills-measure-limit
bash scripts/check.sh
lake build
```

A successful replay establishes compilation in the pinned environment. It is reproducibility evidence, not external certification of the physical theorem.

## Current priorities

1. Resolve the discrete finite-time versus real continuum-time parameter boundary and instantiate the scale-dependent temporal action without assuming an invalid group identification.
2. Prove interpolation equivariance and obtain continuum Euclidean-time invariance for the selected physical embedding.
3. Construct continuum reflection, instantiate `WeakLimitTimeReflectionBridge`, and derive the concrete self-adjoint OS Hamiltonian.
4. Complete branch-wide CI and terminal aggregate-import registration.
5. Prove vacuum uniqueness, continuum clustering, and a positive physical spectral gap.
6. Complete the physical continuum carrier, scaling trajectory, regularity, nontriviality, and independent review.

## Public claim boundary

Recommended wording:

```text
MGAP4D is a Lean 4 formal-development repository for a four-dimensional
Yang--Mills construction and mass-gap proof architecture. It contains concrete
finite periodic SU(N) Wilson probability laws, exact gauge and periodic
translation invariance, a concrete integer temporal-translation subgroup,
finite Dobrushin and heat-bath gap theorems, conditional common-carrier
weak-limit constructions, finite and weak-limit reflection-positivity routes,
and a gauge-invariant OS Hilbert/semigroup construction whose closed right
Hamiltonian has a finite-time Laplace resolvent and positive-shift
surjectivity. Self-adjointness is proved once the concrete continuum
reflection/time-translation covariance bridge is supplied. A physically
justified nontrivial continuum theory, vacuum uniqueness, a positive physical
spectral gap, and any independent derivation of 33/20 remain open.
```
