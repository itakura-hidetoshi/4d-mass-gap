# MGAP4D

**MGAP4D** is Hidetoshi Itakura's canonical Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

```text
Canonical repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
Authoritative proof status: docs/current_proof_status.md
Development roadmap: ROADMAP.md
```

## Current status — 2026-07-01

This repository is a replayable formal-development surface.

It does **not** yet establish an unconditional interacting four-dimensional continuum Yang--Mills theory, a nontrivial continuum limit from one fully specified physical scaling trajectory, or a physical mass gap derived from that trajectory.

The repository currently has two distinct proof surfaces.

```text
main
  authoritative merged release surface
  finite Wilson and Dobrushin mathematics
  finite SU(N) Haar--Gibbs and reflection-positive theory
  conditional weak-limit, OS Hilbert, Hamiltonian, and gap-transfer constructors

formal/real-hilbert-uniform-coercive-strong-limit
  integrated post-main proof carrier
  native compact Haar heat-bath L2 theory
  uniform finite-volume spectral certificates
  coercive transport across varying Hilbert spaces
  OS semigroup-defect and strong-resolvent limits
  Painleve--Kuratowski convergence of finite-time operator graphs
```

A theorem on the active proof carrier is not a theorem on `main` until it has been reconciled with current `main`, reviewed, merged, and replayed there.

A theorem that accepts a positive mass slope, a strict Dobrushin estimate, a coercive compactness bound, a physical interpolation package, or a self-adjoint OS Hamiltonian as an input remains conditional until those inputs are constructed for the intended physical Yang--Mills family.

## Repository snapshot

```text
latest mathematical proof checkpoint on main:
  a80a75449a16d07889519c1823595c5244824583

latest merged mathematical proof PR on main:
  PR #300 — oriented canonical Dobrushin coefficient and compact Wilson gap lane

current main documentation head:
  e20a26cc3034c2e5c793d371b034585ab57cc385

active proof carrier:
  formal/real-hilbert-uniform-coercive-strong-limit
  7f1dae659bef10ea1713d57d20a620d1065fbf1d

latest integrated proof PR on the carrier:
  PR #364 — Package canonical strong resolvent and graph convergence

latest carrier validation:
  PR #364 head 67428df16f4057b7956f2b873a90c639572d070d
  PR Lean Fast Check run 5205 — success
```

PR #328's earlier `No goals to be solved` failure has been repaired.

Its final head `ba8b9e09856dd419e577a6861addd8f0893c7b56` passed **PR Lean Fast Check** run 5151 and was merged into the active proof carrier.

Relative to the current `main` documentation head, the active carrier is reported as:

```text
ahead:       359 commits
behind:      169 commits
merge base:  929e20583ae368475d4bedb65c060c2d3c4c0fff
```

The carrier is replay-clean at its current head but is not ready for direct promotion to `main` without deliberate reconciliation and decomposition.

## Proved on `main`

### Finite Wilson probability and reflection positivity

The merged source constructs a finite periodic compact-gauge Wilson theory with:

```text
positive physical links
  -> normalized product Haar probability
  -> Wilson Gibbs probability measure
  -> finite gauge and translation invariance
  -> even-periodic reflection geometry
  -> boundary/open-half Haar factorization
  -> Wilson Gibbs density factorization
  -> local positive-semidefinite crossing kernels
  -> finite Gibbs reflection positivity.
```

For the standard `SU(N)` Wilson plaquette energy

```text
E_W(U) = 1 - Re(trace U) / N,
```

the source proves continuity, conjugation invariance, inversion compatibility, and

```text
0 <= E_W(U) <= 2.
```

These are finite-volume results, not a continuum existence theorem.

### Orientation-correct Dobrushin and finite heat-bath theory

The merged physical-link lane contains:

```text
exact oriented single-link conditional law
  -> target-local / target-remote action decomposition
  -> exact remote-factor cancellation
  -> exact conditional total-variation influence
  -> plaquette-support locality
  -> exact row sums and canonical Dobrushin coefficient
  -> proof-carrying Dobrushin matrix
  -> variation and random-scan contraction
  -> Gibbs Hilbert realization
  -> Rayleigh and Poincare inequalities
  -> normalized finite heat-bath Hamiltonian gap.
```

For periodic four-dimensional geometry with side length at least three, the source supplies the active-neighbor bound `18` and the one-shared-plaquette bound used by the coefficient estimate.

The compact-group interfaces package `alpha < 1` into finite-volume vacuum-sector coercivity, lower real spectral enclosures, and resolvent estimates.

This closes a finite theorem generator from a strict coefficient to a finite Hamiltonian gap.

It does not prove a scale-uniform strict coefficient along the physical continuum trajectory.

### Conditional physical weak limits

Given explicit interpolation or blocking maps, lattice spacing and volume data, a coupling trajectory, a proper compactness functional, and a coercive moment estimate, the merged common-carrier framework derives uniform moments and tails, compact containment and tightness, a Prokhorov subsequence, bounded-continuous expectation convergence, and gauge and translation invariance under the required equivariance hypotheses.

The physical carrier, interpolation, scaling data, compactness estimate, and nontriviality theorem remain open model-specific inputs.

### OS Hilbert space and Hamiltonian

From a continuum reflection-positive state with the required covariance, contraction, symmetry, and continuity data, the merged source constructs:

```text
positive-time gauge-invariant observables
  -> OS bilinear form and null quotient
  -> real Hilbert completion
  -> normalized vacuum and dense state map
  -> strongly continuous contraction semigroup
  -> right generator and Hamiltonian
  -> graph closure
  -> nonnegative self-adjoint Hamiltonian
  -> real resolvent estimates.
```

This is a formal reconstruction package from explicit hypotheses.

The repository does not yet generate every hypothesis from one concrete nontrivial continuum Yang--Mills measure.

### Conditional continuum mass-gap transfer

The merged source accepts a positive scale-uniform finite-side estimate or an equivalent transfer-operator contraction certificate of the form

```text
(1 - exp (-mass * t)) * ||v||^2
  <= ||v||^2 - ||K_(n,t) v||^2,

mass > 0.
```

It then derives a vacuum-orthogonal Hamiltonian Rayleigh bound, lower real spectral enclosure, real resolvent estimates, vacuum-line uniqueness at zero energy, and exclusion of nonzero eigenvectors below the supplied mass.

The required physical scale-uniform estimate is not yet derived from the actual four-dimensional scaling trajectory.

## Integrated active proof carrier

### Finite explicit and native compact heat-bath layers

The active carrier contains the explicit periodic oriented `Z2` small-coupling theorem with sufficient condition

```text
beta < log (19 / 17) / 2.
```

The corresponding PR #302 remains open against `main`.

The carrier also contains the native compact-group one-link Haar heat-bath kernel, exact conditional Gibbs measures, stationarity, detailed balance, `L2` conditional-expectation projections, random-scan positivity, Poincare inequalities, finite Hamiltonians, uniform Dobrushin resolvents, lower spectral enclosures, and bundled finite-volume spectral-gap certificates.

### Coercive strong-limit transport

The carrier proves that uniform coercive symmetric lower bounds pass to a common real Hilbert carrier under exact identifications and then under asymptotic approximation maps and isometric embeddings:

```text
uniform coercivity and symmetry
  -> coercive limit form
  -> Lax--Milgram inverse
  -> shifted real resolvents
  -> lower real spectral enclosure
  -> inverse-distance resolvent bounds.
```

Compact-Wilson wrappers apply this generic analysis to uniformly controlled finite-volume families.

The approximation maps and their convergence remain hypotheses until a physical interpolation theorem supplies them.

### OS strong-resolvent convergence

PRs #317--#328 construct the vacuum-orthogonal rescaled semigroup defects, their common half-mass coercive bound, convergence on the canonical Hamiltonian core, dense core-shift range, and full strong convergence of resolvents.

For every

```text
lambda < mass / 2
```

and every excitation vector `y`, the carrier proves

```text
R_tau(lambda) y -> R(lambda) y,
```

where `R_tau(lambda)` is the bounded resolvent of the admissible rescaled defect and `R(lambda)` is the resolvent of the graph-closed continuum excitation Hamiltonian.

It also proves the equivalent norm-to-zero statement.

### Operator-graph convergence

PRs #332--#363 extend the resolvent theorem to graph convergence.

The development includes resolvent-selected graph-pair convergence, approximation of every continuum Hamiltonian graph point, exact and approximate shifted-defect graph limits, varying shifts and right-hand sides, arbitrary nontrivial filters, filter Painleve--Kuratowski inner and outer limits, recovery nets, and outer-limit containment.

The final canonical theorem removes auxiliary source, shift, time-net, and filter-nontriviality arguments from its public interface.

It states that both filter Painleve--Kuratowski limits of the ordinary finite-time rescaled-defect graphs equal the graph of the closed continuum excitation Hamiltonian.

PR #364 packages this graph theorem with the below-gap strong-resolvent theorem under one common interface.

These results remain conditional on the supplied positive `VacuumSemigroupGapSlope`, normalized OS data, inner symmetry, self-adjointness, and the physical construction that generates those objects.

They do not imply norm-resolvent convergence, unrestricted closure of the union of all finite-time graphs, or convergence of every spectral projection without additional hypotheses.

## Current theorem boundary

| Surface | Status |
|---|---|
| Finite compact Wilson Haar--Gibbs probability theory | proved on `main` |
| Finite even-periodic Wilson reflection positivity | proved on `main` |
| Orientation-correct canonical Dobrushin coefficient | proved on `main` |
| Finite random-scan, Poincare, and heat-bath gap from `alpha < 1` | proved on `main` |
| Conditional physical weak-limit constructor | proved on `main` from explicit hypotheses |
| Conditional OS Hilbert and self-adjoint Hamiltonian constructor | proved on `main` from explicit hypotheses |
| Conditional continuum mass-gap transfer | proved on `main` from a supplied positive certificate |
| Explicit periodic oriented `Z2` threshold | active carrier; PR #302 open against `main` |
| Native compact Haar heat-bath `L2` theory | integrated on active carrier |
| Uniform compact Wilson finite-volume spectral certificate | integrated on active carrier |
| Coercive varying-Hilbert strong-limit transport | integrated on active carrier |
| Full OS strong-resolvent convergence | integrated on active carrier; CI green |
| Canonical operator-graph Painleve--Kuratowski convergence | integrated on active carrier; CI green |
| Canonical combined operator-limit package | PR #364 integrated on active carrier; CI green |
| Promotion of the active carrier to `main` | not completed |
| Concrete gauge-compatible continuum carrier and interpolation | open |
| Renormalized coupling and scaling trajectory | open |
| Nontrivial interacting continuum limit | open |
| Uniform positive gap for the physical approximation family | open |
| Fully instantiated OS/Wightman reconstruction | open |
| Physical numerical mass value and units | open |
| Independent external mathematical consensus | not claimed |

## Exact `33/20` lane

The repository transports the normalized value `33/20` through internal Hamiltonian, spectral, and audit interfaces.

This is an internal normalization and dependency-routing surface.

It is not an independent derivation of the physical four-dimensional Yang--Mills mass gap and is not identified with the conditional Wilson/OS `mass` parameter.

See `docs/exact_gap_layer_separation.md`.

## Primary review anchors

| Topic | File |
|---|---|
| Authoritative proof status | `docs/current_proof_status.md` |
| Development roadmap | `ROADMAP.md` |
| Finite Wilson reflection positivity | `MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenWilsonGibbsReflectionPositivity.lean` |
| Oriented Dobrushin coefficient | `MGAP4D/MathlibAnalytic/FiniteOrientedLatticeWilsonCanonicalDobrushinCoefficient.lean` |
| Finite heat-bath Hamiltonian gap | `MGAP4D/MathlibAnalytic/FiniteOrientedWilsonCanonicalDobrushinHamiltonianGap.lean` |
| Physical weak-limit constructor | `MGAP4D/MathlibAnalytic/PeriodicHypercubicSpecialUnitaryWeakLimit.lean` |
| OS Hamiltonian spine | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSHamiltonianSpine.lean` |
| Full strong resolvent | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSFullStrongResolvent.lean` on the active carrier |
| Ordinary operator-graph convergence | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSOperatorGraphKuratowskiConvergence.lean` on the active carrier |
| Canonical graph theorem | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSOperatorGraphKuratowskiCanonicalFilter.lean` on the active carrier |
| Canonical combined package | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSCanonicalOperatorLimitPackage.lean` on the active carrier |
| Exact-gap separation | `docs/exact_gap_layer_separation.md` |

## Replay

Pinned toolchain:

```text
Lean:    leanprover/lean4:v4.30.0-rc2
mathlib: v4.30.0-rc2
```

Replay `main`:

```bash
git clone https://github.com/itakura-hidetoshi/4d-mass-gap.git
cd 4d-mass-gap
bash scripts/check.sh
lake build
```

Replay the active proof carrier:

```bash
git checkout formal/real-hilbert-uniform-coercive-strong-limit
bash scripts/check.sh
lake build
```

A successful replay verifies that the declared Lean statements elaborate and their proofs replay in the pinned environment.

It is reproducibility evidence, not external certification that the physical hypotheses have been discharged.

## Immediate priorities

1. Reconcile the active proof carrier with current `main` and remove the 169-commit backward divergence.
2. Decompose the carrier into reviewable finite, generic functional-analytic, and continuum OS merge units.
3. Promote the explicit finite `Z2`, native compact Haar heat-bath, uniform spectral, strong-limit, strong-resolvent, and graph-limit layers in dependency order.
4. Instantiate one concrete gauge-compatible continuum carrier, interpolation scheme, scaling trajectory, and nontriviality argument.
5. Prove a scale-uniform positive gap estimate for that actual physical approximation family.
6. Apply the merged OS Hamiltonian and operator-limit machinery to the instantiated model.
7. Complete the remaining OS/Wightman, physical-normalization, and independent-review obligations.

## License and attribution

Copyright belongs to Hidetoshi Itakura except where third-party licenses apply.

See the repository license files and individual source headers for exact terms.
