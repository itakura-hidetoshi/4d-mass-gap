# MGAP4D

**MGAP4D** is Hidetoshi Itakura's canonical Lean 4 / mathlib repository for a proof-carrying investigation of the four-dimensional Yang--Mills existence and mass-gap problem.

```text
Canonical repository: itakura-hidetoshi/4d-mass-gap
KuuOS reference repository: itakura-hidetoshi/KuuOS
Reference bridge: docs/kuuos_reference_bridge.md
Authoritative proof status: docs/current_proof_status.md
Development roadmap: ROADMAP.md
```

## Current status — 2026-06-30

This repository is a replayable formal-development surface.

It does **not** yet establish an unconditional interacting four-dimensional continuum Yang--Mills theory, a fully instantiated physical Osterwalder--Schrader reconstruction, or a physical mass gap derived from a concrete continuum scaling trajectory.

The source must be read in two layers.

```text
main
  merged finite Wilson and Dobrushin mathematics
  merged finite SU(N) Haar--Gibbs and reflection-positive theory
  merged conditional weak-limit, OS Hilbert, Hamiltonian, and gap-transfer constructors

stacked proof frontier
  native compact-group heat-bath L2 theory
  uniform finite-volume spectral certificates
  coercive strong-limit transport across varying Hilbert spaces
  OS semigroup-defect spectral gaps
  graph-core and full strong-resolvent convergence
```

A frontier result is not a `main` result until it has been rebased, reviewed, merged into `main`, and replayed there.

A theorem that accepts a positive mass slope, a uniform Dobrushin bound, a coercive compactness estimate, or a physical interpolation package as input is conditional until the actual physical Wilson family supplies that input.

## Repository snapshot

```text
latest mathematical proof checkpoint on main:
  a80a75449a16d07889519c1823595c5244824583

latest merged mathematical proof PR:
  PR #300 — oriented canonical Dobrushin coefficient and compact Wilson gap lane

large physical construction merged into main:
  PR #282
  merge commit ed42e5af631aec11f16c7095c3cd892b488bd04d

current stacked frontier:
  PR #328 — Prove full OS strong-resolvent convergence
  head 540cc5848626fce2a69fff6948e14886e9591277
  base formal/real-hilbert-uniform-coercive-strong-limit
  base commit a846a06aa286f4d0beb624bfd5e461653b797b58
```

At this snapshot, PR #328 is open, non-draft, and reported as mergeable. **PR Lean Fast Check** run 5141 completed with failure while building `PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalCoreGraphApproximation.lean`: line 220 reports `No goals to be solved`. The frontier is not merge-ready until this Lean error is repaired and the branch is replayed successfully.

Relative to the latest mathematical checkpoint `a80a7544…`, the PR #328 head is reported as 237 commits ahead and 157 commits behind, with merge base `929e20583ae368475d4bedb65c060c2d3c4c0fff`. The frontier therefore requires deliberate rebase and decomposition before mathematical promotion to `main`.

## Proved on `main`

### Finite Wilson probability and reflection positivity

The merged source contains a concrete finite periodic compact-gauge Wilson theory with:

```text
positive physical links
  -> normalized product Haar measure
  -> Wilson Gibbs probability measure
  -> finite gauge and translation invariance
  -> even-periodic reflection geometry
  -> boundary/open-half Haar factorization
  -> Wilson Gibbs density factorization
  -> local positive-semidefinite crossing kernels
  -> finite Gibbs reflection positivity.
```

The `SU(N)` specialization uses

```text
E_W(U) = 1 - Re(trace U) / N
```

and proves continuity, conjugation invariance, inversion compatibility, and

```text
0 <= E_W(U) <= 2.
```

These are finite-volume results, not a continuum existence theorem.

### Orientation-correct Dobrushin and heat-bath theory

The merged physical-link lane contains:

```text
exact single-link conditional law
  -> target-local / target-remote action decomposition
  -> exact remote-factor cancellation
  -> exact conditional total-variation influence
  -> plaquette-support locality
  -> exact row sums and canonical Dobrushin coefficient
  -> Dobrushin matrix and variation contraction
  -> random-scan contraction
  -> Gibbs Hilbert realization
  -> Rayleigh and Poincare inequalities
  -> normalized heat-bath Hamiltonian gap.
```

For periodic four-dimensional geometry with side length at least three, the source supplies the active-neighbor bound `18` and the one-shared-plaquette bound used by the coefficient estimate.

The compact-group lane packages `alpha < 1` into finite-volume vacuum-sector coercivity, lower spectral enclosures, and real resolvent estimates.

This closes the finite theorem generator from a strict coefficient to a finite heat-bath Hamiltonian gap. It does not prove a scale-uniform strict coefficient along the physical continuum trajectory.

### Conditional physical weak limits

Given explicit interpolation or blocking maps, lattice spacing and volume data, a coupling trajectory, a proper compactness functional, and a coercive moment estimate, the merged common-carrier framework derives:

- uniform moments and tails;
- compact containment and tightness;
- a Prokhorov subsequence;
- bounded-continuous expectation convergence;
- gauge and translation invariance under the required equivariance hypotheses.

The physical carrier, scaling data, compactness estimate, and nontriviality proof remain open inputs.

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

This is a formal reconstruction package from explicit hypotheses. The repository does not yet instantiate every hypothesis from one concrete nontrivial continuum Yang--Mills measure.

### Conditional continuum mass-gap transfer

A positive scale-uniform finite-side estimate or equivalent transfer-operator contraction certificate is supplied:

```text
(1 - exp (-mass * t)) * ||v||^2
  <= ||v||^2 - ||K_(n,t) v||^2,

mass > 0.
```

The formal theory then derives a vacuum-orthogonal Hamiltonian Rayleigh bound, lower real spectral enclosure, resolvent estimates, vacuum-line uniqueness at zero energy, and exclusion of nonzero eigenvectors below the supplied mass.

The required physical scale-uniform estimate is not yet derived from the actual four-dimensional scaling trajectory.

## Stacked proof frontier

### Explicit finite and native compact heat-bath layers

PR #302 packages an explicit periodic oriented `Z2` finite small-coupling theorem with the sufficient condition

```text
beta < log (19 / 17) / 2.
```

PRs #303--#309 construct the native compact-group one-link Haar heat-bath kernel, its `L2` conditional-expectation projection, reversibility, Poincare and Hamiltonian structures, uniform Dobrushin resolvents, lower spectral enclosures, and a bundled finite-volume spectral-gap certificate.

### Strong-limit transport

PRs #310--#316 prove that a uniform coercive symmetric gap passes to a common Hilbert carrier under exact identifications and then under asymptotic approximation maps and isometric embeddings:

```text
uniform coercivity and symmetry
  -> coercive limit form
  -> Lax--Milgram inverse
  -> shifted resolvents
  -> lower spectral enclosure
  -> compact Wilson specialization.
```

### OS defects and full strong-resolvent convergence

PRs #317--#321 prove spectral bounds for `I - T(t)` and for the rescaled defects `t^(-1)(I - T(t))` on the vacuum-orthogonal Hilbert sector. A supplied positive mass slope yields a common half-mass coercive bound for sufficiently small positive times.

PRs #322--#326 prove convergence on the canonical Hamiltonian core, resolvent convergence on the core-shift range, a generic dense-range extension theorem, vacuum-orthogonal graph-core approximation, and density of the core-shift range.

PR #328 combines these ingredients. For every

```text
lambda < mass / 2
```

and every excitation vector `y`, it proves strong convergence of the bounded rescaled-defect resolvents to the graph-closed continuum excitation-Hamiltonian resolvent:

```text
R_tau(lambda) y -> R(lambda) y.
```

It also proves the equivalent norm-to-zero statement.

This remains conditional on the positive mass slope, OS semigroup package, self-adjointness, and physical approximation data used to generate those structures. Its current CI failure is an implementation defect in the graph-core approximation file and must be repaired before the frontier can be treated as replayed.

## Current theorem boundary

| Surface | Status |
|---|---|
| Finite compact Wilson Haar--Gibbs probability theory | proved on `main` |
| Finite even-periodic Wilson reflection positivity | proved on `main` |
| Orientation-correct canonical Dobrushin coefficient | proved on `main` |
| Finite random-scan, Poincare, and heat-bath gap from `alpha < 1` | proved on `main` |
| Explicit periodic oriented `Z2` threshold theorem | PR #302, not on `main` |
| Native compact Haar heat-bath `L2` theory | stacked frontier |
| Uniform compact Wilson finite-volume spectral certificate | stacked frontier |
| Coercive varying-Hilbert strong-limit transport | stacked frontier |
| Full OS strong-resolvent convergence | PR #328, Lean CI failed at this snapshot |
| Concrete gauge-compatible continuum carrier and interpolation | open |
| Renormalized coupling and scaling trajectory | open |
| Uniform positive gap for the physical approximation family | open |
| Nontrivial interacting continuum limit | open |
| Fully instantiated OS/Wightman reconstruction | open |
| Physical numerical mass value and units | open |
| Independent external mathematical consensus | not claimed |

## Exact `33/20` lane

The repository transports the normalized value `33/20` through internal Hamiltonian, spectral, and audit interfaces.

This is an internal normalization and dependency-routing surface. It is not an independent derivation of the physical four-dimensional Yang--Mills mass gap and is not identified with the conditional Wilson/OS `mass` parameter.

See `docs/exact_gap_layer_separation.md`.

## Primary review anchors

| Topic | File |
|---|---|
| Authoritative proof status | `docs/current_proof_status.md` |
| Development roadmap | `ROADMAP.md` |
| Finite Wilson reflection positivity | `MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenWilsonGibbsReflectionPositivity.lean` |
| Oriented Dobrushin coefficient | `MGAP4D/MathlibAnalytic/FiniteOrientedLatticeWilsonCanonicalDobrushinCoefficient.lean` |
| Four-dimensional compact Wilson certificate | `MGAP4D/MathlibAnalytic/ContinuousCompactOrientedGaugeWilsonFourDimensionalDobrushinCertificate.lean` |
| Finite heat-bath Hamiltonian gap | `MGAP4D/MathlibAnalytic/FiniteOrientedWilsonCanonicalDobrushinHamiltonianGap.lean` |
| Physical weak-limit constructor | `MGAP4D/MathlibAnalytic/PeriodicHypercubicSpecialUnitaryWeakLimit.lean` |
| OS Hamiltonian spine | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSHamiltonianSpine.lean` |
| Conditional boundary-gap closure | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSApproximatingExponentialBoundaryGapClosure.lean` |
| Frontier full strong resolvent | `MGAP4D/MathlibAnalytic/PhysicalYangMillsGaugeInvariantOSFullStrongResolvent.lean` in PR #328 |
| Exact-gap separation | `docs/exact_gap_layer_separation.md` |

## Replay

Pinned toolchain:

```text
Lean:    leanprover/lean4:v4.30.0-rc2
mathlib: v4.30.0-rc2
```

```bash
git clone https://github.com/itakura-hidetoshi/4d-mass-gap.git
cd 4d-mass-gap
bash scripts/check.sh
lake build
```

A successful replay verifies the declared Lean source in the pinned environment. It is reproducibility evidence, not external certification of the physical theorem.

## Immediate priorities

1. Repair the PR #328 graph-core approximation error at line 220 and obtain green CI.
2. Rebase and decompose the stacked frontier against current `main`.
3. Merge the explicit finite `Z2`, native compact Haar heat-bath, uniform spectral, strong-limit, and strong-resolvent layers in dependency order.
4. Instantiate one concrete gauge-compatible continuum carrier, interpolation scheme, scaling trajectory, and nontriviality argument.
5. Prove a scale-uniform positive gap estimate for that actual physical approximation family.
6. Apply the merged OS Hamiltonian and strong-resolvent machinery to the instantiated model.
7. Complete the remaining OS/Wightman, physical-normalization, and external-review obligations.

## License and attribution

Copyright belongs to Hidetoshi Itakura except where third-party licenses apply.

See the repository license files and individual source headers for exact terms.
