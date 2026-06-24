# MGAP4D

**MGAP4D** is Hidetoshi Itakura's canonical Lean 4 / Mathlib repository for a proof-carrying investigation of four-dimensional Yang--Mills theory and the mass-gap problem.

```text
Canonical repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
```

## Current status — 2026-06-24

The repository is an active formal-development and review surface. It is **not** a completed or externally validated solution of the four-dimensional Yang--Mills existence and mass-gap problem.

Two checkpoints must be distinguished.

```text
main:
  finite Wilson heat-bath, exact Dobrushin, finite Hamiltonian-gap,
  and transfer-orbit implication layers through merged PR #274

active branch:
  physical-4d-yang-mills-measure-limit
  PR #282, open, non-draft, mergeable
```

The code snapshot used for this documentation update is:

```text
PR #282 code baseline: 54b3404d5096ec007f757e1c288d472bc3ac8a3d
```

At that baseline, the dedicated `Temporary Periodic Translation Check` run 3 succeeded. The ordinary `PR Lean Fast Check` run 4274 was cancelled before the changed-Lean build completed. Therefore this README does **not** claim a final ordinary-CI green result for the complete current PR head.

## Current concrete proof spine

The active development now contains several connected but logically distinct lanes.

```text
finite periodic SU(N) Wilson geometry and Haar--Gibbs laws
  -> exact gauge invariance
  -> exact periodic translation invariance
  -> finite Wilson conditional laws and exact Dobrushin influence control
  -> finite heat-bath Poincare and Hamiltonian-gap consequences
  -> physical lattice embeddings into a common Polish carrier
  -> tightness and Prokhorov subsequential weak limits
  -> continuum gauge-symmetry transfer
  -> bounded observable, correlation, and finite n-point convergence
  -> even-periodic Wilson reflection positivity
  -> weak-limit reflection-positive quadratic observables
  -> gauge-invariant positive-time observable algebra
  -> OS pre-Hilbert quotient and Hilbert completion
  -> positive-time contraction semigroup
  -> strong continuity on the completed physical Hilbert space
  -> dense right-generator domain
  -> closable nonnegative right Hamiltonian
  -> graph-closed Hamiltonian
  -> finite-time Laplace resolvent
  -> positive-shift surjectivity
  -> self-adjointness once the OS reflection/time-translation symmetry bridge is supplied.
```

The arrows above do not all have the same status. Some are unconditional finite-volume theorems. Some are theorem-generated transfers from explicit structures. Some still require model-dependent continuum bridge data.

## 1. Finite Wilson and exact Dobrushin lane

The finite Wilson lane is concrete. It starts from actual finite-volume Wilson Gibbs laws and exact one-link conditional distributions.

It includes:

- finite Wilson action and normalized Gibbs probability laws;
- exact single-link conditional laws;
- conditional-expectation projections `P_e`;
- fluctuation projections `Q_e = I - P_e`;
- detailed balance, Gibbs symmetry, orthogonality, and weighted Pythagoras;
- the concrete finite Gibbs Hilbert realization;
- the canonical heat-bath Hamiltonian
  `H_HB = sum_e Q_e`;
- the exact scaling identity
  `H_HB = |E| (I - P_scan)`;
- canonical Dobrushin random-scan Rayleigh contraction;
- exact active/shared-plaquette localization of Wilson influence;
- finite-volume and family finite-gap consequences in the stated Dobrushin regime;
- transfer-orbit contraction packages built from those finite gaps.

The former README statement that the Dobrushin TV-to-centered-`L²` theorem was open is obsolete. That finite analytic conversion and the exact plaquette-supported influence route were completed before the current PR, through merged PR #274.

This does not yet identify the finite heat-bath Hamiltonian with the continuum physical OS Hamiltonian.

## 2. Physical weak-limit and gauge-symmetry lane

PR #282 constructs typed routes from actual finite periodic `SU(N)` Wilson Gibbs laws to subsequential probability measures on one supplied physical Polish carrier.

The branch contains:

- signed oriented periodic Wilson geometry;
- normalized Haar--Gibbs probability measures;
- exact finite gauge invariance;
- exact plaquette cardinality and normalized action bounds;
- lattice embeddings and interpolation interfaces;
- proper/coercive functional interfaces;
- compact containment and tightness;
- Prokhorov subsequences;
- weak convergence to a `PhysicalFourDimensionalYangMillsWeakLimit`;
- transfer of continuous gauge actions to the limiting law;
- invariant event probabilities and observable laws;
- convergence and invariance of bounded continuous expectations;
- two-point, connected-correlation, and finite n-point observable routes;
- the real algebra of gauge-invariant bounded continuous observables.

The weak-limit constructor is mathematically explicit but physically conditional. The repository still needs a justified distributional carrier, a concrete interpolation or blocking map, a renormalized coupling trajectory, and a coercive estimate appropriate to the intended continuum Yang--Mills theory.

## 3. Finite and weak-limit reflection positivity

The even-periodic Wilson lane constructs finite-volume Osterwalder--Schrader positivity from boundary-fibered coordinates, Haar factorization, temporal-sector decomposition, and Gram/RKHS kernels.

The terminal finite theorem is exposed through:

```lean
periodicHypercubicEvenWilsonGibbs_reflectionPositive_boundedContinuous
```

For a fixed bounded continuous physical quadratic observable, the branch provides a bridge from the actual finite Wilson reflected observable to the physical approximating measures and proves that nonnegativity passes to the weak limit.

This is a genuine weak-convergence theorem. It is not yet a construction of every positive-time continuum observable required by the full OS axiom system.

## 4. Gauge-invariant OS Hilbert and Hamiltonian lane

The branch constructs the following analytic route on supplied gauge-invariant OS data:

```text
positive-time observable algebra
  -> OS bilinear form
  -> null-space quotient
  -> real pre-Hilbert carrier
  -> Hilbert completion
  -> dense physical-state map
  -> positive-time contraction semigroup
  -> observable-state strong continuity
  -> strongly continuous physical contraction semigroup
  -> right infinitesimal generator
  -> right Hamiltonian H = -G
  -> dense domain from Bochner time averages
  -> nonnegative quadratic form
  -> closability
  -> graph closure Hbar
  -> resolvent lower bound and closed range
  -> finite-time Laplace resolvent identity
  -> surjectivity of lambda I + Hbar for lambda > 0
  -> bijectivity and maximal-accretive package.
```

The finite-time Laplace resolvent has removed positive-shift surjectivity as an independent assumption.

The self-adjointness theorem has the exact remaining hypothesis:

```text
formal symmetry of Hbar
```

The branch proves formal symmetry from symmetry of the completed Euclidean semigroup, and semigroup symmetry from the observable reflection/time-translation exchange identity.

Thus the terminal result is currently conditional on a concrete `WeakLimitTimeReflectionBridge` or equivalent covariance package connecting:

- continuum Euclidean-time translations;
- configuration reflection;
- gauge covariance;
- positive-time restriction;
- continuum-state identification;
- observable-state strong continuity.

## 5. Translation invariance and the present frontier

The newest concrete finite-volume result proves invariance of the periodic `SU(N)` Wilson system under every periodic lattice displacement.

It includes:

- vertex, edge, plaquette, and configuration translation equivalences;
- covariance of signed boundary steps;
- covariance of plaquette holonomy;
- invariance of the Wilson action;
- invariance of product normalized Haar measure;
- invariance of the finite Wilson Gibbs probability law.

This finite translation theorem passed its dedicated workflow on code baseline `54b3404d...`.

The next nontrivial step is not another finite reindexing lemma. It is to construct and verify the continuum temporal-action package:

```text
finite periodic translations
  -> lattice temporal translations at every approximation scale
  -> interpolation equivariance
  -> embedded-law invariance
  -> continuum Euclidean-time invariance
  -> reflection/time-translation exchange
  -> semigroup symmetry
  -> self-adjoint closed OS Hamiltonian.
```

## What the repository currently establishes

| Surface | Current reading |
|---|---|
| Finite periodic `SU(N)` Wilson Gibbs law | Concrete |
| Finite gauge invariance | Proved |
| Finite periodic translation invariance | Proved in PR #282 source; dedicated check succeeded |
| Exact Wilson Dobrushin locality and centered Rayleigh contraction | Proved before PR #282 |
| Finite heat-bath Hamiltonian gap in the stated regime | Proved |
| Common-carrier weak-limit extraction | Constructed from explicit embedding/coercivity hypotheses |
| Continuum gauge invariance | Proved from continuous action and interpolation-equivariance data |
| Finite even-periodic reflection positivity | Proved |
| Fixed bounded continuous OS quadratic observable at the weak limit | Proved from the pullback bridge |
| Gauge-invariant OS Hilbert completion | Constructed from supplied reflection-positive state data |
| Strongly continuous physical contraction semigroup | Constructed from observable-state continuity |
| Dense, closable, nonnegative right Hamiltonian | Implemented in PR #282 source |
| Positive-shift surjectivity of the closed Hamiltonian | Implemented by the finite-time Laplace resolvent route |
| Self-adjointness of the closed Hamiltonian | Proved from the concrete OS covariance/symmetry bridge |
| Concrete continuum OS covariance bridge | Still open |
| Positive spectral gap of the constructed OS Hamiltonian | Open |
| Vacuum uniqueness and nontriviality | Open |
| Physical continuum Yang--Mills construction | Open |
| Physical derivation of `33/20` | Not established |
| External mathematical consensus | Not claimed |

## Exact `33/20` boundary

The source tree contains an internal normalized value `33/20` carried through older spectral, PVM, R6, and R7 interfaces.

That lane is an internal normalization and dependency-audit surface. It is not an independent derivation of the physical four-dimensional Yang--Mills mass gap.

The current OS Hamiltonian lane does not yet prove:

- that its spectral gap is positive;
- that its gap equals `33/20`;
- that the physical normalization converting lattice or semigroup parameters to physical units yields `33/20`.

Read `docs/exact_gap_layer_separation.md` for the dependency-level separation.

## Primary review anchors

| Topic | File |
|---|---|
| Concise status | `docs/current_proof_status.md` |
| Development plan | `ROADMAP.md` |
| Physical measure frontier | `docs/physical_yang_mills_measure_frontier.md` |
| Gauge-symmetry observable spine | `docs/physical_yang_mills_symmetry_observable_spine.md` |
| Finite translation invariance | `MGAP4D/MathlibAnalytic/PeriodicHypercubicTranslationInvariance.lean` |
| Finite bounded-continuous reflection positivity | `MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenWilsonGibbsBoundedContinuousReflectionPositivity.lean` |
| Weak-limit OS nonnegativity | `MGAP4D/MathlibAnalytic/PhysicalYangMillsEvenPeriodicWilsonOSWeakLimit.lean` |
| Gauge-invariant OS Hilbert completion | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSHilbertCompletion.lean` |
| Positive-time contraction | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSPositiveTimeContraction.lean` |
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

From a fresh clone:

```bash
git clone https://github.com/itakura-hidetoshi/4d-mass-gap.git
cd 4d-mass-gap
git checkout physical-4d-yang-mills-measure-limit
bash scripts/check.sh
lake build
```

A successful replay proves that the selected Lean source compiles in the pinned environment. It is reproducibility evidence, not external certification of the physical theorem.

## Current priorities

1. Connect the concrete periodic translation theorem to the lattice temporal-action and interpolation-equivariance interfaces.
2. Construct the continuum reflection/time-translation covariance bridge and discharge the remaining symmetry input to OS Hamiltonian self-adjointness.
3. Obtain a final ordinary PR Lean Fast Check on the complete branch head and register the terminal aggregate imports.
4. Prove vacuum uniqueness, identify the physical spectrum, and derive a strictly positive spectral gap for the constructed OS Hamiltonian.
5. Supply the physically justified continuum carrier, scaling trajectory, regularity, nontriviality, and independent review.

## Public claim boundary

Recommended wording:

```text
MGAP4D is a Lean 4 formal-development repository for a four-dimensional
Yang--Mills construction and mass-gap proof architecture. It contains concrete
finite periodic SU(N) Wilson probability laws, exact gauge and translation
invariance, finite Dobrushin and heat-bath gap theorems, conditional
common-carrier weak-limit constructions, finite and weak-limit
reflection-positivity routes, and a gauge-invariant OS Hilbert/semigroup
construction whose closed right Hamiltonian has a finite-time Laplace
resolvent and positive-shift surjectivity. Self-adjointness is proved once the
concrete continuum reflection/time-translation covariance bridge is supplied.
A physically justified nontrivial continuum theory, vacuum uniqueness,
a positive physical spectral gap, and any independent derivation of 33/20
remain open.
```
